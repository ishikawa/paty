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
# destructuring
assert '300
400' '
  def foo(t: ("add" | "mul", int64, int64))
    case t
    when ("add", x, y)
      puts(x + y)
    when ("mul", x, y)
      puts(x * y)
    end
  end
  foo(("add", 100, 200))
  foo(("mul", 20, 20))'
assert '300
400' '
  struct T { op: "add" | "mul", x: int64, y: int64 }
  def foo(t: T)
    case t
    when T { op: "add", x, y }
      puts(x + y)
    when T { op: "mul", x: a, y: b }
      puts(a * b)
    end
  end
  foo(T { op: "add", x: 100, y: 200 })
  foo(T { op: "mul", x: 20, y: 20 })'
# destructuring (spread)
assert '{ b: 1, c: 2, d: 3 }
{ c: 2, d: 3 }
{ d: 3 }
{}
16' '
  struct T {
    a: int64,
    b: int64,
    c: int64,
    d: int64,
  }
  def foo(t: T)
    case t
    when T { a: 0, ...x }
      puts(x)
    when T { a: 1, b: 1, ...x }
      puts(x)
    when T { a: 2, b: 2, c: 2, ...x }
      puts(x)
    when T { a: 3, b: 3, c: 3, d: 3, ...x }
      puts(x)
    when T { a, b, c: c, d: x }
      puts(a + b + c + x)
    end
  end
  foo(T { a: 0, b: 1, c: 2, d: 3 })
  foo(T { a: 1, b: 1, c: 2, d: 3 })
  foo(T { a: 2, b: 2, c: 2, d: 3 })
  foo(T { a: 3, b: 3, c: 3, d: 3 })
  foo(T { a: 4, b: 4, c: 4, d: 4 })'
# destructuring (or-pattern)
assert '6
8
9
7
0' '
  struct T {
    a: int64,
    b: int64,
    c: int64,
    d: int64,
  }
  def foo(t: T)
    case t
    when T { a: 0, b: x, c: y, ... } |
        T { a: 1, c: x, b: y, ... } |
        T { a: 2, c: x, d: y, ... } |
        T { a: 3, d: x, c: y, ... }
      puts(x - y)
    else
      puts(0)
    end
  end
  foo(T { a: 0, b: 10, c: 4, d: 3 })
  foo(T { a: 1, b: 1, c: 9, d: 3 })
  foo(T { a: 2, b: 2, c: 12, d: 3 })
  foo(T { a: 3, b: 3, c: 3, d: 10 })
  foo(T { a: 4, b: 4, c: 4, d: 4 })'
# union and or-pattern
assert 'YES
YES
NO
NO' '
  def foo(b: boolean | "yes" | "no")
    case b
    when true | "yes"
      puts("YES")
    when false | "no"
      puts("NO")
    end
  end
  foo(true)
  foo("yes")
  foo(false)
  foo("no")'