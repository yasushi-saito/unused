package main

import (
	"go/ast"
	"go/token"
	"go/types"
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/passes/inspect"
	// "golang.org/x/tools/go/ast/inspector"
	"fmt"
	"golang.org/x/tools/go/types/typeutil"
	"io"
	"log"
	"os"
	"path/filepath"
	"strings"
	"sync"
)

var Pass1Analyzer = &analysis.Analyzer{
	Name:     "pass1",
	Doc:      "todo",
	Run:      func(pass *analysis.Pass) (interface{}, error) { return checker.visit(pass) },
	Requires: []*analysis.Analyzer{inspect.Analyzer},
}

type graph struct {
	roots []*graphNode
	nodes map[interface{}]*graphNode
	seq   int
}

type Checker struct {
	WholeProgram       bool
	ConsiderReflection bool
	Debug              io.Writer

	mu           sync.Mutex
	pkgs         []*analysis.Pass
	graph        *graph
	msCache      typeutil.MethodSetCache
	topmostCache map[*types.Scope]*types.Scope
	interfaces   []*types.Interface
}

var checker = &Checker{
	WholeProgram: true,
	graph: &graph{
		nodes: map[interface{}]*graphNode{},
		seq:   1,
	},
	topmostCache: map[*types.Scope]*types.Scope{},
}

func (g *graph) markUsedBy(obj, usedBy interface{}) {
	objNode := g.getNode(obj)
	usedByNode := g.getNode(usedBy)
	if objNode.obj == usedByNode.obj {
		return
	}
	usedByNode.uses[objNode] = struct{}{}
	// log.Printf("adddep %v<-%v", objNode, usedByNode)
}

type graphNode struct {
	obj   interface{}
	uses  map[*graphNode]struct{}
	used  bool
	quiet bool
	n     int
}

func (c *Checker) visit(pass *analysis.Pass) (interface{}, error) {
	c.mu.Lock()
	c.pkgs = append(c.pkgs, pass)
	c.mu.Unlock()
	return nil, nil
}

func (c *Checker) findExportedInterfaces() {
	c.interfaces = []*types.Interface{types.Universe.Lookup("error").Type().(*types.Named).Underlying().(*types.Interface)}
	for _, pass := range c.pkgs {
		for _, tv := range pass.TypesInfo.Types {
			iface, ok := tv.Type.(*types.Interface)
			if !ok {
				continue
			}
			if iface.NumMethods() == 0 {
				continue
			}
			//log.Printf("Adding interface %+v", iface)
			c.interfaces = append(c.interfaces, iface)
		}
	}
}

func (c *Checker) checkPackage(pass *analysis.Pass) {
	c.processDefs(pass)
	c.processUses(pass)
	c.processTypes(pass)
	c.processSelections(pass)
	c.processAST(pass)
}

func (g *graph) getNode(obj interface{}) *graphNode {
	for {
		if pt, ok := obj.(*types.Pointer); ok {
			obj = pt.Elem()
		} else {
			break
		}
	}
	_, ok := g.nodes[obj]
	if !ok {
		g.addObj(obj)
	}
	return g.nodes[obj]
}

func (g *graph) addObj(obj interface{}) {
	if pt, ok := obj.(*types.Pointer); ok {
		obj = pt.Elem()
	}
	node := &graphNode{obj: obj, uses: make(map[*graphNode]struct{}), n: g.seq}
	g.nodes[obj] = node
	g.seq++

	if obj, ok := obj.(*types.Struct); ok {
		n := obj.NumFields()
		for i := 0; i < n; i++ {
			field := obj.Field(i)
			g.markUsedBy(obj, field)
		}
	}
}

func (c *Checker) processDefs(pass *analysis.Pass) {
	for _, obj := range pass.TypesInfo.Defs {
		if obj == nil {
			continue
		}
		c.graph.getNode(obj)

		if obj, ok := obj.(*types.TypeName); ok {
			c.graph.markUsedBy(obj.Type().Underlying(), obj.Type())
			c.graph.markUsedBy(obj.Type(), obj) // TODO is this needed?
			c.graph.markUsedBy(obj, obj.Type())

			// We mark all exported fields as used. For normal
			// operation, we have to. The user may use these fields
			// without us knowing.
			//
			// TODO(dh): In whole-program mode, however, we mark them
			// as used because of reflection (such as JSON
			// marshaling). Strictly speaking, we would only need to
			// mark them used if an instance of the type was
			// accessible via an interface value.
			if !c.WholeProgram || c.ConsiderReflection {
				c.useExportedFields(obj.Type())
			}

			// TODO(dh): Traditionally we have not marked all exported
			// methods as exported, even though they're strictly
			// speaking accessible through reflection. We've done that
			// because using methods just via reflection is rare, and
			// not worth the false negatives. With the new -reflect
			// flag, however, we should reconsider that choice.
			if !c.WholeProgram {
				c.useExportedMethods(obj.Type())
			}
		}

		switch obj := obj.(type) {
		case *types.Var, *types.Const, *types.Func, *types.TypeName:
			if obj.Exported() {
				// Exported variables and constants use their types,
				// even if there's no expression using them in the
				// checked program.
				//
				// Also operates on funcs and type names, but that's
				// irrelevant/redundant.
				c.graph.markUsedBy(obj.Type(), obj)
			}
			if obj.Name() == "_" {
				node := c.graph.getNode(obj)
				node.quiet = true
				scope := c.topmostScope(pass.Pkg.Scope().Innermost(obj.Pos()), pass.Pkg)
				if scope == pass.Pkg.Scope() {
					c.graph.roots = append(c.graph.roots, node)
				} else {
					c.graph.markUsedBy(obj, scope)
				}
			} else {
				// Variables declared in functions are used. This is
				// done so that arguments and return parameters are
				// always marked as used.
				if _, ok := obj.(*types.Var); ok {
					if obj.Parent() != obj.Pkg().Scope() && obj.Parent() != nil {
						c.graph.markUsedBy(obj, c.topmostScope(obj.Parent(), obj.Pkg()))
						c.graph.markUsedBy(obj.Type(), obj)
					}
				}
			}
		}

		if fn, ok := obj.(*types.Func); ok {
			// A function uses its signature
			c.graph.markUsedBy(fn, fn.Type())

			// A function uses its return types
			sig := fn.Type().(*types.Signature)
			res := sig.Results()
			n := res.Len()
			for i := 0; i < n; i++ {
				c.graph.markUsedBy(res.At(i).Type(), fn)
			}
		}

		if obj, ok := obj.(interface {
			Scope() *types.Scope
			Pkg() *types.Package
		}); ok {
			scope := obj.Scope()
			c.graph.markUsedBy(c.topmostScope(scope, obj.Pkg()), obj)
		}

		if c.isRoot(pass, obj) {
			node := c.graph.getNode(obj)
			c.graph.roots = append(c.graph.roots, node)
			if obj, ok := obj.(*types.PkgName); ok {
				scope := obj.Pkg().Scope()
				c.graph.markUsedBy(scope, obj)
			}
		}
	}
}

// func (c *Checker) processDef(pass *analysis.Pass, obj types.Object) {
// 	if typ, ok := obj.(*types.TypeName); ok {
// 		c.graph.markUsedBy(typ.Type().Underlying(), typ.Type())
// 		c.graph.markUsedBy(typ.Type(), typ) // is this needed?
// 		c.graph.markUsedBy(typ, typ.Type())
// 	}
// 	switch obj := obj.(type) {
// 	case *types.Var, *types.Const, *types.Func, *types.TypeName:
// 		if obj.Exported() {
// 			// Exported variables and constants use their types,
// 			// even if there's no expression using them in the
// 			// checked program.
// 			//
// 			// Also operates on funcs and type names, but that's
// 			// irrelevant/redundant.
// 			c.graph.markUsedBy(obj.Type(), obj)
// 		}
// 		if obj.Name() == "_" {
// 			node := c.graph.getNode(obj)
// 			node.quiet = true
// 			scope := c.topmostScope(pass.Pkg.Scope().Innermost(obj.Pos()), pass.Pkg)
// 			if scope == pass.Pkg.Scope() {
// 				c.graph.roots = append(c.graph.roots, node)
// 			} else {
// 				c.graph.markUsedBy(obj, scope)
// 			}
// 		} else {
// 			// Variables declared in functions are used. This is
// 			// done so that arguments and return parameters are
// 			// always marked as used.
// 			if _, ok := obj.(*types.Var); ok {
// 				if obj.Parent() != obj.Pkg().Scope() && obj.Parent() != nil {
// 					c.graph.markUsedBy(obj, c.topmostScope(obj.Parent(), obj.Pkg()))
// 					c.graph.markUsedBy(obj.Type(), obj)
// 				}
// 			}
// 		}
// 	}

// 	if fn, ok := obj.(*types.Func); ok {
// 		// A function uses its signature
// 		c.graph.markUsedBy(fn, fn.Type())

// 		// A function uses its return types
// 		sig := fn.Type().(*types.Signature)
// 		res := sig.Results()
// 		n := res.Len()
// 		for i := 0; i < n; i++ {
// 			c.graph.markUsedBy(res.At(i).Type(), fn)
// 		}
// 	}

// 	if obj, ok := obj.(interface {
// 		Scope() *types.Scope
// 		Pkg() *types.Package
// 	}); ok {
// 		scope := obj.Scope()
// 		c.graph.markUsedBy(c.topmostScope(scope, obj.Pkg()), obj)
// 	}

// 	if c.isRoot(pass, obj) {
// 		node := c.graph.getNode(obj)
// 		c.graph.roots = append(c.graph.roots, node)
// 		if obj, ok := obj.(*types.PkgName); ok {
// 			scope := obj.Pkg().Scope()
// 			c.graph.markUsedBy(scope, obj)
// 		}
// 	}
// }

func (c *Checker) topmostScope(scope *types.Scope, pkg *types.Package) (ret *types.Scope) {
	if top, ok := c.topmostCache[scope]; ok {
		return top
	}
	defer func() {
		c.topmostCache[scope] = ret
	}()
	if scope == pkg.Scope() {
		return scope
	}
	if scope.Parent().Parent() == pkg.Scope() {
		return scope
	}
	return c.topmostScope(scope.Parent(), pkg)
}

func (c *Checker) processUses(pass *analysis.Pass) (interface{}, error) {
	for ident, usedObj := range pass.TypesInfo.Uses {
		if _, ok := usedObj.(*types.PkgName); ok {
			continue
		}
		pos := ident.Pos()
		scope := pass.Pkg.Scope().Innermost(pos)
		scope = c.topmostScope(scope, pass.Pkg)
		if scope != pass.Pkg.Scope() {
			c.graph.markUsedBy(usedObj, scope)
		}

		switch usedObj.(type) {
		case *types.Var, *types.Const:
			c.graph.markUsedBy(usedObj.Type(), usedObj)
		}
	}
	return nil, nil
}

func (c *Checker) processTypes(pass *analysis.Pass) (interface{}, error) {
	named := map[*types.Named]*types.Pointer{}
	var interfaces []*types.Interface
	for _, tv := range pass.TypesInfo.Types {
		if typ, ok := tv.Type.(interface {
			Elem() types.Type
		}); ok {
			c.graph.markUsedBy(typ.Elem(), typ)
		}

		switch obj := tv.Type.(type) {
		case *types.Named:
			named[obj] = types.NewPointer(obj)
			c.graph.markUsedBy(obj, obj.Underlying())
			c.graph.markUsedBy(obj.Underlying(), obj)
		case *types.Interface:
			if obj.NumMethods() > 0 {
				interfaces = append(interfaces, obj)
			}
		case *types.Struct:
			c.useNoCopyFields(obj)
			if pass.Pkg.Name() != "main" && !c.WholeProgram {
				c.useExportedFields(obj)
			}
		}
	}

	// Pretend that all types are meant to implement as many
	// interfaces as possible.
	//
	// TODO(dh): For normal operations, that's the best we can do, as
	// we have no idea what external users will do with our types. In
	// whole-program mode, we could be more conservative, in two ways:
	// 1) Only consider interfaces if a type has been assigned to one
	// 2) Use SSA and flow analysis and determine the exact set of
	// interfaces that is relevant.
	fn := func(iface *types.Interface) {
		for obj, objPtr := range named {
			if !types.Implements(obj, iface) && !types.Implements(objPtr, iface) {
				continue
			}
			ifaceMethods := make(map[string]struct{}, iface.NumMethods())
			n := iface.NumMethods()
			for i := 0; i < n; i++ {
				meth := iface.Method(i)
				ifaceMethods[meth.Name()] = struct{}{}
			}
			for _, obj := range []types.Type{obj, objPtr} {
				ms := c.msCache.MethodSet(obj)
				n := ms.Len()
				for i := 0; i < n; i++ {
					sel := ms.At(i)
					meth := sel.Obj().(*types.Func)
					_, found := ifaceMethods[meth.Name()]
					if !found {
						continue
					}
					c.graph.markUsedBy(meth.Type().(*types.Signature).Recv().Type(), obj) // embedded receiver
					if len(sel.Index()) > 1 {
						f := getField(obj, sel.Index()[0])
						c.graph.markUsedBy(f, obj) // embedded receiver
					}
					c.graph.markUsedBy(meth, obj)
				}
			}
		}
	}

	for _, iface := range interfaces {
		fn(iface)
	}
	for _, iface := range c.interfaces {
		fn(iface)
	}
	return nil, nil
}

// inspect := pass.ResultOf[inspect.Analyzer].(*inspector.Inspector)
// nodeFilter := []ast.Node{
// 	(*ast.GenDecl)(nil),
// 	(*ast.FuncDecl)(nil),
// 	(*ast.CallExpr)(nil),
// }
// inspect.Nodes(nodeFilter, func(n ast.Node, push bool) (prune bool) {
// 	switch v := n.(type) {
// 	case *ast.GenDecl:
// 		if v.Tok == token.TYPE {
// 			for _, spec := range v.Specs {
// 				typ := pass.TypesInfo.Defs[spec.(*ast.TypeSpec).Name].(*types.TypeName)

// 			}
// 		} else if v.Tok == token.VAR {
// 			for _, spec := range v.Specs {
// 				log.Printf("Var %+v push %v", spec, prune)
// 			}
// 		}
// 		return false
// 	case *ast.FuncDecl:
// 		fdecl := v
// 		fn := pass.TypesInfo.Defs[fdecl.Name].(*types.Func)
// 		name := fn.FullName()
// 		if push {
// 			u.markUsedBy(fn.FullName(), fdecl.Name.Pos())
// 			u.push(name)
// 			log.Printf("FN: %+v %v push=%v", fn, fn.FullName(), push)
// 		} else {
// 			u.pop(name)
// 			log.Printf("FN: %+v %v push=%v", fn, fn.FullName(), push)
// 		}
// 		return true
// 	case *ast.CallExpr:
// 		call := v
// 		fn, _ := typeutil.Callee(pass.TypesInfo, call).(*types.Func)
// 		if fn == nil {
// 			return
// 		}
// 		log.Printf("CALL: %+v %s push=%v", fn, fn.FullName(), push)
// 		u.markUsedBy(u.top(), fn.FullName())
// 		return true
// 	}
// 	panic("blah")
// })

func findFuncDecls(pass *analysis.Pass) (interface{}, error) {
	for _, file := range pass.Files {
		for _, decl := range file.Decls {
			fdecl, ok := decl.(*ast.FuncDecl)
			if !ok || fdecl.Body == nil {
				continue
			}
			//fn := pass.TypesInfo.Defs[fdecl.Name].(*types.Func)
			// log.Printf("FN: %+v %v", fn, fn.FullName())
		}
	}
	return nil, nil
}

func isFunction(obj types.Object) bool {
	_, ok := obj.(*types.Func)
	return ok
}
func isMethod(obj types.Object) bool {
	if !isFunction(obj) {
		return false
	}
	return obj.(*types.Func).Type().(*types.Signature).Recv() != nil
}

func isVariable(obj types.Object) bool {
	_, ok := obj.(*types.Var)
	return ok
}

func isConstant(obj types.Object) bool {
	_, ok := obj.(*types.Const)
	return ok
}

func isType(obj types.Object) bool {
	_, ok := obj.(*types.TypeName)
	return ok
}

func isField(obj types.Object) bool {
	if obj, ok := obj.(*types.Var); ok && obj.IsField() {
		return true
	}
	return false
}

func isBasicStruct(elts []ast.Expr) bool {
	for _, elt := range elts {
		if _, ok := elt.(*ast.KeyValueExpr); !ok {
			return true
		}
	}
	return false
}

func isPkgScope(obj types.Object) bool {
	return obj.Parent() == obj.Pkg().Scope()
}

func isMain(obj types.Object) bool {
	if obj.Pkg().Name() != "main" {
		return false
	}
	if obj.Name() != "main" {
		return false
	}
	if !isPkgScope(obj) {
		return false
	}
	if !isFunction(obj) {
		return false
	}
	if isMethod(obj) {
		return false
	}
	return true
}
func (c *Checker) isRoot(pass *analysis.Pass, obj types.Object) bool {

	// - in local mode, main, init, tests, and non-test, non-main exported are roots
	// - in global mode (not yet implemented), main, init and tests are roots

	if _, ok := obj.(*types.PkgName); ok {
		return true
	}

	if strings.Index(obj.Name(), "GLOBAL") >= 0 {
		log.Printf("XXXXX %v", obj.Name())
		return true
	}
	if isFunction(obj) {
		x := obj.(*types.Func)
		if strings.Index(x.FullName(), "GLOBAL") >= 0 {
			return true
		}
	}

	if isMain(obj) || (isFunction(obj) && !isMethod(obj) && obj.Name() == "init") {
		return true
	}
	if obj.Exported() {
		f := pass.Fset.Position(obj.Pos()).Filename
		if strings.HasSuffix(f, "_test.go") {
			return strings.HasPrefix(obj.Name(), "Test") ||
				strings.HasPrefix(obj.Name(), "Benchmark") ||
				strings.HasPrefix(obj.Name(), "Example")
		}

		// Package-level are used, except in package main
		if isPkgScope(obj) && obj.Pkg().Name() != "main" && false {
			return true
		}
	}
	return false
}

// isNoCopyType reports whether a type represents the NoCopy sentinel
// type. The NoCopy type is a named struct with no fields and exactly
// one method `func Lock()` that is empty.
//
// FIXME(dh): currently we're not checking that the function body is
// empty.
func isNoCopyType(typ types.Type) bool {
	st, ok := typ.Underlying().(*types.Struct)
	if !ok {
		return false
	}
	if st.NumFields() != 0 {
		return false
	}

	named, ok := typ.(*types.Named)
	if !ok {
		return false
	}
	if named.NumMethods() != 1 {
		return false
	}
	meth := named.Method(0)
	if meth.Name() != "Lock" {
		return false
	}
	sig := meth.Type().(*types.Signature)
	if sig.Params().Len() != 0 || sig.Results().Len() != 0 {
		return false
	}
	return true
}

func (c *Checker) useNoCopyFields(typ types.Type) {
	if st, ok := typ.Underlying().(*types.Struct); ok {
		n := st.NumFields()
		for i := 0; i < n; i++ {
			field := st.Field(i)
			if isNoCopyType(field.Type()) {
				c.graph.markUsedBy(field, typ)
				c.graph.markUsedBy(field.Type().(*types.Named).Method(0), field.Type())
			}
		}
	}
}

func (c *Checker) useExportedFields(typ types.Type) {
	if st, ok := typ.Underlying().(*types.Struct); ok {
		n := st.NumFields()
		for i := 0; i < n; i++ {
			field := st.Field(i)
			if field.Exported() {
				c.graph.markUsedBy(field, typ)
			}
		}
	}
}

func (c *Checker) useExportedMethods(typ types.Type) {
	named, ok := typ.(*types.Named)
	if !ok {
		return
	}
	ms := typeutil.IntuitiveMethodSet(named, &c.msCache)
	for i := 0; i < len(ms); i++ {
		meth := ms[i].Obj()
		if meth.Exported() {
			c.graph.markUsedBy(meth, typ)
		}
	}

	st, ok := named.Underlying().(*types.Struct)
	if !ok {
		return
	}
	n := st.NumFields()
	for i := 0; i < n; i++ {
		field := st.Field(i)
		if !field.Anonymous() {
			continue
		}
		ms := typeutil.IntuitiveMethodSet(field.Type(), &c.msCache)
		for j := 0; j < len(ms); j++ {
			if ms[j].Obj().Exported() {
				c.graph.markUsedBy(field, typ)
				break
			}
		}
	}
}

func getField(typ types.Type, idx int) *types.Var {
	switch obj := typ.(type) {
	case *types.Pointer:
		return getField(obj.Elem(), idx)
	case *types.Named:
		switch v := obj.Underlying().(type) {
		case *types.Struct:
			return v.Field(idx)
		case *types.Pointer:
			return getField(v.Elem(), idx)
		default:
			panic(fmt.Sprintf("unexpected type %s", typ))
		}
	case *types.Struct:
		return obj.Field(idx)
	}
	return nil
}

func (c *Checker) processSelections(pass *analysis.Pass) {
	fn := func(expr *ast.SelectorExpr, sel *types.Selection, offset int) {
		scope := pass.Pkg.Scope().Innermost(expr.Pos())
		c.graph.markUsedBy(expr.X, c.topmostScope(scope, pass.Pkg))
		c.graph.markUsedBy(sel.Obj(), expr.X)
		if len(sel.Index()) > 1 {
			typ := sel.Recv()
			indices := sel.Index()
			for _, idx := range indices[:len(indices)-offset] {
				obj := getField(typ, idx)
				typ = obj.Type()
				c.graph.markUsedBy(obj, expr.X)
			}
		}
	}

	for expr, sel := range pass.TypesInfo.Selections {
		switch sel.Kind() {
		case types.FieldVal:
			fn(expr, sel, 0)
		case types.MethodVal:
			fn(expr, sel, 1)
		}
	}
}

func dereferenceType(typ types.Type) types.Type {
	if typ, ok := typ.(*types.Pointer); ok {
		return typ.Elem()
	}
	return typ
}

// processConversion marks fields as used if they're part of a type conversion.
func (c *Checker) processConversion(pass *analysis.Pass, node ast.Node) {
	if node, ok := node.(*ast.CallExpr); ok {
		callTyp := pass.TypesInfo.Types[node.Fun]
		var typDst *types.Struct
		var ok bool
		switch typ := callTyp.Type.(type) {
		case *types.Named:
			typDst, ok = typ.Underlying().(*types.Struct)
		case *types.Pointer:
			typDst, ok = typ.Elem().Underlying().(*types.Struct)
		default:
			return
		}
		if !ok {
			return
		}

		if typ, ok := pass.TypesInfo.TypeOf(node.Args[0]).(*types.Basic); ok && typ.Kind() == types.UnsafePointer {
			// This is an unsafe conversion. Assume that all the
			// fields are relevant (they are, because of memory
			// layout)
			n := typDst.NumFields()
			for i := 0; i < n; i++ {
				c.graph.markUsedBy(typDst.Field(i), typDst)
			}
			return
		}

		typSrc, ok := dereferenceType(pass.TypesInfo.TypeOf(node.Args[0])).Underlying().(*types.Struct)
		if !ok {
			return
		}

		// When we convert from type t1 to t2, were t1 and t2 are
		// structs, all fields are relevant, as otherwise the
		// conversion would fail.
		//
		// We mark t2's fields as used by t1's fields, and vice
		// versa. That way, if no code actually refers to a field
		// in either type, it's still correctly marked as unused.
		// If a field is used in either struct, it's implicitly
		// relevant in the other one, too.
		//
		// It works in a similar way for conversions between types
		// of two packages, only that the extra information in the
		// graph is redundant unless we're in whole program mode.
		n := typDst.NumFields()
		for i := 0; i < n; i++ {
			fDst := typDst.Field(i)
			fSrc := typSrc.Field(i)
			c.graph.markUsedBy(fDst, fSrc)
			c.graph.markUsedBy(fSrc, fDst)
		}
	}
}

func (c *Checker) markFields(typ types.Type) {
	structType, ok := typ.Underlying().(*types.Struct)
	if !ok {
		return
	}
	n := structType.NumFields()
	for i := 0; i < n; i++ {
		field := structType.Field(i)
		c.graph.markUsedBy(field, typ)
	}
}

// processCompositeLiteral marks fields as used if the struct is used
// in a composite literal.
func (c *Checker) processCompositeLiteral(pass *analysis.Pass, node ast.Node) {
	// XXX how does this actually work? wouldn't it match t{}?
	if node, ok := node.(*ast.CompositeLit); ok {
		typ := pass.TypesInfo.TypeOf(node)
		if _, ok := typ.(*types.Named); ok {
			typ = typ.Underlying()
		}
		if _, ok := typ.(*types.Struct); !ok {
			return
		}

		if isBasicStruct(node.Elts) {
			c.markFields(typ)
		}
	}
}

// processCgoExported marks functions as used if they're being
// exported to cgo.
func (c *Checker) processCgoExported(pass *analysis.Pass, node ast.Node) {
	if node, ok := node.(*ast.FuncDecl); ok {
		if node.Doc == nil {
			return
		}
		for _, cmt := range node.Doc.List {
			if !strings.HasPrefix(cmt.Text, "//go:cgo_export_") {
				return
			}
			obj := pass.TypesInfo.ObjectOf(node.Name)
			c.graph.roots = append(c.graph.roots, c.graph.getNode(obj))
		}
	}
}

func (c *Checker) processVariableDeclaration(pass *analysis.Pass, node ast.Node) {
	if decl, ok := node.(*ast.GenDecl); ok {
		for _, spec := range decl.Specs {
			spec, ok := spec.(*ast.ValueSpec)
			if !ok {
				continue
			}
			for i, name := range spec.Names {
				if i >= len(spec.Values) {
					break
				}
				value := spec.Values[i]
				fn := func(node ast.Node) bool {
					if node3, ok := node.(*ast.Ident); ok {
						obj := pass.TypesInfo.ObjectOf(node3)
						if _, ok := obj.(*types.PkgName); ok {
							return true
						}
						c.graph.markUsedBy(obj, pass.TypesInfo.ObjectOf(name))
					}
					return true
				}
				ast.Inspect(value, fn)
			}
		}
	}
}

func (c *Checker) processArrayConstants(pass *analysis.Pass, node ast.Node) {
	if decl, ok := node.(*ast.ArrayType); ok {
		ident, ok := decl.Len.(*ast.Ident)
		if !ok {
			return
		}
		c.graph.markUsedBy(pass.TypesInfo.ObjectOf(ident), pass.TypesInfo.TypeOf(decl))
	}
}

func (c *Checker) processKnownReflectMethodCallers(pass *analysis.Pass, node ast.Node) {
	call, ok := node.(*ast.CallExpr)
	if !ok {
		return
	}
	sel, ok := call.Fun.(*ast.SelectorExpr)
	if !ok {
		return
	}
	if true { // !IsType(pass.TypesInfo.TypeOf(sel.X].Type, "*net/rpc.Server") {
		x, ok := sel.X.(*ast.Ident)
		if !ok {
			return
		}
		pkgname, ok := pass.TypesInfo.ObjectOf(x).(*types.PkgName)
		if !ok {
			return
		}
		if pkgname.Imported().Path() != "net/rpc" {
			return
		}
	}

	var arg ast.Expr
	switch sel.Sel.Name {
	case "Register":
		if len(call.Args) != 1 {
			return
		}
		arg = call.Args[0]
	case "RegisterName":
		if len(call.Args) != 2 {
			return
		}
		arg = call.Args[1]
	}
	typ := pass.TypesInfo.TypeOf(arg)
	ms := types.NewMethodSet(typ)
	for i := 0; i < ms.Len(); i++ {
		c.graph.markUsedBy(ms.At(i).Obj(), typ)
	}
}

func (c *Checker) processAST(pass *analysis.Pass) {
	fn := func(node ast.Node) bool {
		c.processConversion(pass, node)
		c.processKnownReflectMethodCallers(pass, node)
		c.processCompositeLiteral(pass, node)
		c.processCgoExported(pass, node)
		c.processVariableDeclaration(pass, node)
		c.processArrayConstants(pass, node)
		return true
	}
	for _, file := range pass.Files {
		ast.Inspect(file, fn)
	}
}

func markNodesUsed(nodes map[*graphNode]struct{}) {
	for node := range nodes {
		wasUsed := node.used
		node.used = true
		if !wasUsed {
			markNodesUsed(node.uses)
		}
	}
}

func (c *Checker) checkFlags(v interface{}) bool {
	return true
}

func (c *Checker) markNodesQuiet() {
	for _, node := range c.graph.nodes {
		if node.used {
			continue
		}
		if obj, ok := node.obj.(types.Object); ok && !c.checkFlags(obj) {
			node.quiet = true
			continue
		}
		c.markObjQuiet(node.obj)
	}
}

func (c *Checker) markObjQuiet(obj interface{}) {
	switch obj := obj.(type) {
	case *types.Named:
		n := obj.NumMethods()
		for i := 0; i < n; i++ {
			meth := obj.Method(i)
			node := c.graph.getNode(meth)
			node.quiet = true
			c.markObjQuiet(meth.Scope())
		}
	case *types.Struct:
		n := obj.NumFields()
		for i := 0; i < n; i++ {
			field := obj.Field(i)
			c.graph.nodes[field].quiet = true
		}
	case *types.Func:
		c.markObjQuiet(obj.Scope())
	case *types.Scope:
		if obj == nil {
			return
		}
		if obj.Parent() == types.Universe {
			return
		}
		for _, name := range obj.Names() {
			v := obj.Lookup(name)
			if n, ok := c.graph.nodes[v]; ok {
				n.quiet = true
			}
		}
		n := obj.NumChildren()
		for i := 0; i < n; i++ {
			c.markObjQuiet(obj.Child(i))
		}
	}
}

type Unused struct {
	Obj      types.Object
	Position token.Position
}

func (c *Checker) findUnused() []Unused {
	var unused []Unused
	for _, node := range c.graph.nodes {
		obj, ok := node.obj.(types.Object)
		if !ok {
			continue
		}
		typNode, ok := c.graph.nodes[obj.Type()]
		if !ok {
			continue
		}
		node.uses[typNode] = struct{}{}
	}

	roots := map[*graphNode]struct{}{}
	for _, root := range c.graph.roots {
		roots[root] = struct{}{}
	}
	markNodesUsed(roots)
	c.markNodesQuiet()

	if c.Debug != nil {
		c.printDebugGraph(c.Debug)
	}

	for _, node := range c.graph.nodes {
		if node.used || node.quiet {
			continue
		}
		obj, ok := node.obj.(types.Object)
		if !ok {
			continue
		}
		var xpkg *analysis.Pass
		if !false {
			for _, pkg := range c.pkgs {
				if pkg.Pkg == obj.Pkg() {
					xpkg = pkg
					break
				}
			}
		}
		if xpkg == nil {
			continue
		}

		pos := xpkg.Fset.Position(obj.Pos())
		if pos.Filename == "" || filepath.Base(pos.Filename) == "C" {
			continue
		}
		generated := false
		for _, file := range xpkg.Files {
			if xpkg.Fset.Position(file.Pos()).Filename != pos.Filename {
				continue
			}
			if strings.HasSuffix(pos.Filename, "vdl.go") {
				generated = true
				break
			}
			if len(file.Comments) > 0 {
				generated = isGenerated(file.Comments[0].Text())
			}
			break
		}
		if generated {
			continue
		}
		unused = append(unused, Unused{Obj: obj, Position: pos})
	}
	return unused
}

func typString(obj types.Object) string {
	switch obj := obj.(type) {
	case *types.Func:
		return "func"
	case *types.Var:
		if obj.IsField() {
			return "field"
		}
		return "var"
	case *types.Const:
		return "const"
	case *types.TypeName:
		return "type"
	default:
		// log.Printf("%T", obj)
		return "identifier"
	}
}

func postProcess() {
	checker.findExportedInterfaces()
	for _, pass := range checker.pkgs {
		checker.checkPackage(pass)
	}
	// checker.findExportedInterfaces()
	unused := checker.findUnused()
	for _, u := range unused {
		name := u.Obj.Name()
		if sig, ok := u.Obj.Type().(*types.Signature); ok && sig.Recv() != nil {
			switch sig.Recv().Type().(type) {
			case *types.Named, *types.Pointer:
				typ := types.TypeString(sig.Recv().Type(), func(*types.Package) string { return "" })
				if len(typ) > 0 && typ[0] == '*' {
					name = fmt.Sprintf("(%s).%s", typ, u.Obj.Name())
				} else if len(typ) > 0 {
					name = fmt.Sprintf("%s.%s", typ, u.Obj.Name())
				}
			}
		}
		fmt.Fprintf(os.Stderr, "%v: %s %s is unused\n", u.Position, typString(u.Obj), name)
	}
}

func (c *Checker) printDebugGraph(w io.Writer) {
	fmt.Fprintln(w, "digraph {")
	fmt.Fprintln(w, "n0 [label = roots]")
	for _, node := range c.graph.nodes {
		s := fmt.Sprintf("%s (%T)", node.obj, node.obj)
		s = strings.Replace(s, "\n", "", -1)
		s = strings.Replace(s, `"`, "", -1)
		fmt.Fprintf(w, `n%d [label = %q]`, node.n, s)
		color := "black"
		switch {
		case node.used:
			color = "green"
		case node.quiet:
			color = "orange"
		case !c.checkFlags(node.obj):
			color = "purple"
		default:
			color = "red"
		}
		fmt.Fprintf(w, "[color = %s]", color)
		fmt.Fprintln(w)
	}

	for _, node1 := range c.graph.nodes {
		for node2 := range node1.uses {
			fmt.Fprintf(w, "n%d -> n%d\n", node1.n, node2.n)
		}
	}
	for _, root := range c.graph.roots {
		fmt.Fprintf(w, "n0 -> n%d\n", root.n)
	}
	fmt.Fprintln(w, "}")
}

func isGenerated(comment string) bool {
	return strings.Contains(comment, "Code generated by") ||
		strings.Contains(comment, "DO NOT EDIT")
}
