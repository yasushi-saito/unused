#!/usr/bin/env python3.6

import subprocess

import logging
import re
import os
import glob
from typing import Iterable, List, Set

class TargetDirs:
    def __init__(self) -> None:
        self.__dirs: Set[str] = set()
        self.__libs: List[str] = []
        self.__include_dirs: List[str] = []

    def __add_target_dir(self, path: str) -> None:
        if path in self.__dirs:
            return
        self.__dirs.add(path)
        self.__libs += glob.glob(f'{REPO_ROOT}/bazel-bin/' + path + '/*.a')
        self.__include_dirs.append(path)

    def libs(self) -> List[str]:
        return self.__libs

    def include_dirs(self) -> List[str]:
        return self.__include_dirs

    def add_target(self, target: str) -> None:
        m = re.match(r'//([^:]+):', target)
        if m:
            self.__add_target_dir(m[1])
            return
        m = re.match('@([^/]+)//([^:]*):', target)
        if m:
            self.__add_target_dir(f'external/{m[1]}/{m[2]}')
            return
        raise Exception(f'Illegal dir {target}')

REPO_ROOT = '/home/ysaito/src0'
GOPATH = REPO_ROOT + '/go'
GOROOT = '/home/ysaito/.gimme/versions/go1.11.linux.amd64'
UNUSED_PATH = '/home/ysaito/go/src/github.com/yasushi-saito/unused/unused'

def list_go_packages() -> List[str]:
    packages: List[str] = []
    for root, dirs, files in os.walk(GOPATH):
        has_go = False
        for f in files:
            if f.endswith(".go"):
                has_go = True
                break
        if not has_go:
            continue
        if root.find('vendor') >= 0:
            continue
        if root.find('.cache') >= 0:
            continue
        if root.find('automation/') >= 0:
            continue
        #if root.find('grail-query') < 0 and not root.endswith('grail.com/testutil'):
        #    continue
        packages.append(root)

    return packages

def find_cgo_libs() -> TargetDirs:
    dirs = TargetDirs()
    subprocess.check_call(['bazel', 'build', '//go/src/grail.com/cgo/...'], cwd=REPO_ROOT)
    for line in subprocess.check_output(
            ['bazel', 'query', 'deps(//go/src/grail.com/cgo/...)'],
            cwd=REPO_ROOT,
            universal_newlines=True).split('\n'):
        line = line.strip()
        if not line:
            continue
        if line.find('_jdk') >= 0:
            continue
        if line.startswith('//go/') or line.startswith('//bazel/') or line.startswith('//tools'):
            continue
        if line.startswith('@io_bazel'):
            continue
        if line.startswith('//external:cc_toolchain'):
            continue
        if line.startswith('@bazel') or line.startswith('@local_config'):
            continue
        dirs.add_target(line)
    return dirs

def main() -> None:
    logging.basicConfig(level=logging.INFO)
    dirs = find_cgo_libs()
    ldflags: List[str] = []
    cflags: List[str] = []
    for lib in dirs.libs():
        dir_path = os.path.dirname(lib)
        filename = os.path.basename(lib)
        if filename.find('.pic') >= 0:
            continue
        m = re.match('lib(.*).a$', filename)
        if not m:
            raise Exception(f'Illegal lib name {filename}')
        ldflags += [f'-L{dir_path}', f'-l{m[1]}']
    cflags += [f'-I{REPO_ROOT}']
    envs = os.environ.copy()
    envs['GOPATH'] = GOPATH
    envs['GOROOT'] = GOROOT
    envs['PATH'] = f'{GOROOT}/bin:' + envs['PATH']
    envs['CGO_LDFLAGS'] = ' '.join(ldflags)
    envs['CGO_CFLAGS'] = ' '.join(cflags)

    packages = list_go_packages()
    standard_packages = [
        'sort',
        'io',
        'encoding',
        'encoding/gob',
        'encoding/json',
        'container/heap',
    ]
    cmdline = [UNUSED_PATH] + standard_packages + packages
    log.debug("CMDLINE %s", cmdline)
    log.debug("CFLAGS %s", envs['CGO_CFLAGS'])
    log.debug("LDFLAGS %s", envs['CGO_LDFLAGS'])
    p = subprocess.Popen(
        [UNUSED_PATH] + standard_packages + packages,
        cwd=REPO_ROOT,
        env=envs,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        universal_newlines=True)
    for line in p.stdout.readlines():
        if line.find(GOROOT) >= 0:
            continue
        #if line.startswith(REPO_ROOT + '/'):
        #    line = line[len(REPO_ROOT + '/'):]
        print(line, end='')
    p.wait()
    #|grep -v //go |grep -v 'bazel_tools' |less

main()
