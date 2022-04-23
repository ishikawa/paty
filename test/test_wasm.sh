#!/bin/bash
# The shell script to test the output of some example programs.
set -e

# color codes
GREEN='\033[0;32m'
RED='\033[0;31m'
RESET='\033[0m' # No Color

WORKDIR="./_tmp"
FILENAME="test_wasm"
CCFLAGS="-std=c11 -Wall -Wpedantic -Wextra"
CCTESTFLAGS="-Werror -Wshadow"

mkdir -p "${WORKDIR}"
i=0
assert() {
  expected="$1"
  input="$2"

  echo -n "$input" > "${WORKDIR}/${FILENAME}${i}.paty"
  ./target/debug/paty --target wasm32-wasi "${WORKDIR}/${FILENAME}${i}.paty" > "${WORKDIR}/${FILENAME}${i}.wat"
  wat2wasm "${WORKDIR}/${FILENAME}${i}.wat" -o "${WORKDIR}/${FILENAME}${i}.wasm"
  actual=$(wasmtime run "${WORKDIR}/${FILENAME}${i}.wasm")

  if [ "$actual" = "$expected" ]; then
    echo -e "${GREEN}OK${RESET}   $i: $input => $actual"
  else
    echo -e "${RED}FAIL${RESET} $i: $input => $expected expected, but got $actual"
    exit 1
  fi

  i=$((i+1))
}

# Hello, World!
assert "Hello, World!" 'puts("Hello, World!")'

echo OK