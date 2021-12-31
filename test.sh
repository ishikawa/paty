#!/bin/bash
# Borrowed from https://www.sigbus.info/compilerbook
set -e

assert() {
  expected="$1"
  input="$2"

  echo -n "$input" > tmp.paty
  ./target/debug/paty tmp.paty > tmp.c
  cc -std=c11 -Wall -o tmp tmp.c
  actual=$(./tmp)

  if [ "$actual" = "$expected" ]; then
    echo "$input => $actual"
  else
    echo "$input => $expected expected, but got $actual"
    exit 1
  fi
}

assert 20211231 "puts(20211231)"
assert 5 "
  five = 5
  puts(five)"
assert 30 "
  def foo(x, y)
    x + y
  end
  puts(foo(10, 20))"

echo OK