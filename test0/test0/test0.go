package test0

import (
	"log"
)

type T0 struct {
	X int
	Y string
}

func (t *T0) Blah() {
	log.Printf("x=%v", t.X)
}

func Blah2() {
	var t T0
	log.Printf("y=%v", t.Y)
}

func Main() {
	var t T0
	t.Blah()
}
