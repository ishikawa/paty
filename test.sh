#!/bin/bash
# Borrowed from https://www.sigbus.info/compilerbook
set -e

CCFLAGS="-std=c11 -Wall -Wpedantic -Wextra"
CCTESTFLAGS="-Werror -Wshadow"

assert() {
  expected="$1"
  input="$2"

  echo -n "$input" > tmp.paty
  ./target/debug/paty tmp.paty > tmp.c
  cc ${CCFLAGS} ${CCTESTFLAGS} -o tmp tmp.c
  actual=$(./tmp)

  if [ "$actual" = "$expected" ]; then
    echo "$input => $actual"
  else
    echo "$input => $expected expected, but got $actual"
    exit 1
  fi
}

# number
assert 20211231 "puts(20211231)"
# variable
assert 5 "
  five = 5
  puts(five)"
# function
assert 30 "
  def foo(x, y)
    x + y
  end
  puts(foo(10, 20))"
# comments
assert 30 "
  # comment 1
  def foo(x, y)
    # comment 2
    # comment 3
    x + y
  end
  # comment 4
  puts(foo(10, 20))"

echo OK