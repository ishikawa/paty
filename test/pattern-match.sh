#!/bin/bash
# The shell script to test pattern matches.
# Borrowed from https://www.sigbus.info/compilerbook
set -e

# color codes
GREEN='\033[0;32m'
RED='\033[0;31m'
RESET='\033[0m' # No Color

WORKDIR="./_tmp"
FILENAME="pattern-match"
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
# struct and union type
assert '🇯🇵
🇬🇧
🇺🇸' '
  type T = { name: "Tokyo" | "London" | "Washington, D.C." }
  def foo(t: T)
    case t
    when { name: "Tokyo" }
      puts("🇯🇵")
    when _: { name: "London" }
      puts("🇬🇧")
    else
      puts("🇺🇸")
    end
  end
  foo({ name: "Tokyo" })
  foo({ name: "London" })
  foo({ name: "Washington, D.C." })'