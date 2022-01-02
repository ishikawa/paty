#!/bin/bash
# The shell script to test error messages of some example programs.
# Borrowed from https://www.sigbus.info/compilerbook
# color codes
GREEN='\033[0;32m'
RED='\033[0;31m'
RESET='\033[0m' # No Color

WORKDIR="./_tmp"
FILENAME="error"

mkdir -p "${WORKDIR}"
i=0
assert() {
  expected="$1"
  input="$2"

  # Write the input to a temporary file
  echo -n "$input" > "${WORKDIR}/${FILENAME}${i}.paty"

  # Compile the file and capture stderr output
  actual=$(./target/debug/paty "${WORKDIR}/${FILENAME}${i}.paty" 2>&1 >/dev/null)

  # Check if output contains an expected substring
  if [[ "$actual" = *"$expected"* ]]; then
    echo -e "${GREEN}OK${RESET}   $i: $input => $actual"
  else
    echo -e "${RED}FAIL${RESET} $i: $input => \"$expected\" expected, but got \"$actual\""
    exit 1
  fi

  i=$((i+1))
}

# undefined variable
assert 'Cannot find variable `x` in scope' "x"
assert 'Cannot find variable `x` in scope' "foo()"
