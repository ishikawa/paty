#!/bin/bash
# The shell script to test the output of some example programs.
# Borrowed from https://www.sigbus.info/compilerbook
set -e

# color codes
GREEN='\033[0;32m'
RED='\033[0;31m'
RESET='\033[0m' # No Color

WORKDIR="./_tmp"
FILENAME="test"
CCFLAGS="-std=c11 -Wall -Wpedantic -Wextra"
CCTESTFLAGS="-Werror -Wshadow"

mkdir -p "${WORKDIR}"
i=0
assert() {
  expected="$1"
  input="$2"

  echo -n "$input" > "${WORKDIR}/${FILENAME}${i}.paty"
  ./target/debug/paty "${WORKDIR}/${FILENAME}${i}.paty" > "${WORKDIR}/${FILENAME}${i}.c"
  cc ${CCFLAGS} ${CCTESTFLAGS} -o "${WORKDIR}/${FILENAME}${i}" "${WORKDIR}/${FILENAME}${i}.c"
  actual=$("${WORKDIR}/${FILENAME}${i}")

  if [ "$actual" = "$expected" ]; then
    echo -e "${GREEN}OK${RESET}   $i: $input => $actual"
  else
    echo -e "${RED}FAIL${RESET} $i: $input => $expected expected, but got $actual"
    exit 1
  fi

  i=$((i+1))
}

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
# pattern match (case)
assert 3 "
  case 3
  when 1
    puts(1)
  when 0..=2
    puts(2)
  else
    puts(3)
  end"
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
# pattern match (case)
assert 3 "
  n = case 3
  when 1
    1
  when 0..=2
    2
  else
    3
  end
  puts(n)"
assert 152 "
  def pt(n)
    case n
    when 0..=5
      n * 2
    when 5..<10
      n * 3
    when 10
      n * 4
    else
      n * 5
    end
  end
  puts(pt(1) + pt(5) + pt(10) + pt(20))"
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
# string
assert "Hello, World!" "
  puts(\"Hello, World!\\n\")
"
assert '1 2 3 4' "
  def fruit_to_num(fruit: string)
    case fruit
    when \"Apple\"
      1
    when \"Orange\"
      2
    when \"Strawberry\"
      3
    else
      4
    end
  end
  puts(
    fruit_to_num(\"Apple\"),
    fruit_to_num(\"Orange\"),
    fruit_to_num(\"Strawberry\"),
    fruit_to_num(\"Grape\")
  )"
# examples
assert 13 "$(cat examples/foo.paty)"
assert 55 "$(cat examples/fib.paty)"

echo OK