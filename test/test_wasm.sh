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

# print primitive value.
assert "Hello, World!" 'puts("Hello, World!")'
assert "12345" 'puts(12345)'
assert "-12345" 'puts(-12345)'
assert "true" 'puts(true)'
assert "false" 'puts(false)'
assert '12345
12345
12345
12345' '
  def puts_i(n: int64)
    puts(n)
  end
  def puts_s(s: string)
    puts(s)
  end
  n = 12345
  s = "12345"
  puts_i(n)
  puts_s(s)
  puts_i(n)
  puts_s(s)'
# number
assert 20211231 "puts(20211231)"
assert -20229116 "puts(-20229116)"
# boolean operators
assert true "puts(10 > 5)"
assert false "puts(10 < 5)"
assert true "puts(10 >= 10)"
assert false "puts(10 <= 5)"
assert true "puts(10 == 10)"
assert false "puts(10 != 10)"
assert true "puts(10 > 5 && 10 > 0)"
assert true "puts(true || false)"
assert true "puts(10 >= (5 * 2) && 100 == (300 / 3))"
# basic arithmetic operations
assert 30 "puts(20 * 3 / 2)"
assert 40 "puts(10 + 20 * 3 / 2)"
assert 45 "puts((10 + 20) * 3 / 2)"
assert -75 "puts(-(10 + 20 * 3) + 5 - 10)"
# variable
assert 5 "
  five = 5
  puts(five)"
assert "33
44" "_ = puts(33)
  puts(44)"
assert "66" "(x, y, z) = (11, 22, 33)
  puts(x + y + z)"
assert "231" "((a, b, c), (d, e), (f,)) = ((11, 22, 33), (44, 55), (66,))
  puts(a + b + c + d + e + f)"
# boolean
assert 'true' "
  n = 5
  case n > 1 && n <= 5
  when true
    puts(true)
  when false
    puts(false)
  end"
assert 'true' "
  def is_positive(n)
    n >= 0
  end
  case is_positive(1)
  when true
    puts(true)
  when false
    puts(false)
  end"
# ---------------------------------
# String
# ---------------------------------
assert 'こんにちは' 'puts("こんにちは")'
assert '\' 'puts("\\")'
# Takes a union value and returns a union value.
assert '2
two' '
  def double(n: 1 | "one")
    case n
    when 1
      2
    when "one"
      "two"
    end
  end
  puts(double(1))
  puts(double("one"))'
# Compares strings.
assert '1 2 3 4' '
  def fruit_to_num(fruit: string)
    case fruit
    when "Apple"
      1
    when "Orange"
      2
    when "Strawberry"
      3
    else
      4
    end
  end
  puts(
    fruit_to_num("Apple"),
    fruit_to_num("Orange"),
    fruit_to_num("Strawberry"),
    fruit_to_num("Grape"))'
# ---------------------------------
# Function
# ---------------------------------
assert 30 "
  def foo(x, y)
    x + y
  end
  puts(foo(10, 20))"
assert 30 "
  def foo((x, y): (int64, int64))
    x + y
  end
  puts(foo((10, 20)))"
assert 30 "
  def foo(_, _, z)
    z
  end
  puts(foo(10, 20, 30))"
# function - return type annotation
assert 30 "
  def foo(x: int64, y: int64): int64
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

# ---------------------------------
# Pattern match (case)
# ---------------------------------
# number
assert '1
2
0' '
  def foo(n: int64)
    case n
    when 1
      puts(1)
    when x: 2
      puts(x)
    else
      puts(0)
    end
  end
  foo(1)
  foo(2)
  foo(100)'
# tuple
assert '1
2
(3, "test 3")' '
  def foo(n: (int64, string))
    case n
    when (1, "test 1")
      puts(1)
    when x: (2, "test 2")
      puts(x.0)
    else
      puts(n)
    end
  end
  foo((1, "test 1"))
  foo((2, "test 2"))
  foo((3, "test 3"))'
# struct
assert '🇯🇵
🇬🇧
🌎' '
  struct T { name: string }
  def foo(t: T)
    case t
    when T { name: "Tokyo" }
      puts("🇯🇵")
    when T { name: "London" }
      puts("🇬🇧")
    when _: T
      puts("🌎")
    end
  end
  foo(T { name: "Tokyo" })
  foo(T { name: "London" })
  foo(T { name: "Washington, D.C." })'

echo OK