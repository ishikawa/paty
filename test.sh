#!/bin/bash
# Borrowed from https://www.sigbus.info/compilerbook
set -e

CCFLAGS="-std=c11 -Wall -Wpedantic -Wextra"
CCTESTFLAGS="-Werror -Wshadow"

i=0
assert() {
  expected="$1"
  input="$2"

  echo -n "$input" > tmp${i}.paty
  ./target/debug/paty tmp${i}.paty > tmp${i}.c
  cc ${CCFLAGS} ${CCTESTFLAGS} -o tmp${i} tmp${i}.c
  actual=$(./tmp${i})

  if [ "$actual" = "$expected" ]; then
    echo "$i: $input => $actual"
  else
    echo "$i: $input => $expected expected, but got $actual"
    exit 1
  fi

  i=$((i+1))
}

# number
assert 20211231 "puts(20211231)"
# basic arithmetic operations
assert 40 "puts(10 + 20 * 3 / 2)"
assert 45 "puts((10 + 20) * 3 / 2)"
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