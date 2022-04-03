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

# todo
# or-pattern contains slightly different patterns
assert '1 2
three 4
5 six
seven eight' '
  struct T1 { value: int64 }
  struct T2 { value: string }
  type T3 = (T1 | T2, int64)
  type T4 = (T1 | T2, string)
  def foo(t: T3 | T4)
    case t
    when (T1 { value } | T2 { value }, x)
      puts(value, x)
    end
  end
  foo((T1 { value: 1 }, 2))             # T3
  foo((T2 { value: "three" }, 4))       # T3
  foo((T1 { value: 5 }, "six"))         # T4
  foo((T2 { value: "seven" }, "eight")) # T4
'
assert '1 two
three 4' '
  def foo(n: (int64, string) | (string, int64))
    case n
    when (x, y)
      # x: int64 | string
      # y: string | int64
      puts(x, y)
    end
  end
  foo((1, "two"))
  foo(("three", 4))'

echo OK