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
assert 'cannot find variable `x` in scope' "x"
# undefined function
assert 'cannot find function `foo` in scope' "foo()"
# unreachable pattern
assert 'Semantic error: unreachable pattern: `1`' "
  n = 100
  case n
  when 1
    puts(1)
  when 1
    puts(1)
  else
    puts(n)
  end"
assert 'Semantic error: unreachable pattern: `false`' "
  case 5 > 3
  when true
    puts(true)
  when false
    puts(false)
  when false
    puts(0)
  end"
assert 'Semantic error: unreachable pattern: `"A"`' "
  case \"A\"
  when \"A\"
    puts(1)
  when \"A\"
    puts(2)
  else
    puts(3)
  end"
assert 'Semantic error: unreachable `else` clause' "
  case 5 > 3
  when true
    puts(true)
  when false
    puts(false)
  else
    puts(0)
  end"
assert 'Semantic error: unreachable pattern: `T { value: 0 }`' "
  struct T { value: int64 }
  t = T { value: 123 }
  case t
  when T { value: _ }
    puts(t)
  when T { value: 0 }
    puts(t)
  end"
assert 'Semantic error: unreachable pattern: `T { value: 0 }`' "
  struct T { value: int64 }
  t = T { value: 123 }
  case t
  when T { ... }
    puts(t)
  when T { value: 0 }
    puts(t)
  end"
assert 'Semantic error: unreachable pattern: `T { value: 0 }`' "
  struct T { value: int64 }
  t = T { value: 123 }
  case t
  when x
    puts(x)
  when T { value: 0 }
    puts(t)
  end"
assert 'Semantic error: unreachable pattern: `T { a: _, b: _ }`' "
  struct T { a: boolean, b: boolean }
  case T { a: true, b: false }
  when T { a: true, b: true }
    puts(1)
  when T { a: true, b: false }
    puts(2)
  when T { a: false, b: true }
    puts(3)
  when T { a: false, b: false }
    puts(4)
  when T { a, b }
    puts(5)
  end"
# non-exhaustive pattern
assert 'Semantic error: non-exhaustive pattern: `int64::MIN..=0`' "
  n = 100
  case n
  when 1
    puts(1)
  when 2
    puts(2)
  end"
assert 'Semantic error: non-exhaustive pattern: `true`' "
  case 5 > 3
  when false
    puts(false)
  end"
assert 'Semantic error: non-exhaustive pattern: `false`' "
  case 5 > 3
  when true
    puts(true)
  end"
assert 'Semantic error: non-exhaustive pattern: `_`' "
  case \"A\"
  when \"A\"
    puts(1)
  when \"B\"
    puts(2)
  end"
assert 'Semantic error: non-exhaustive pattern: `T { a: false, b: false }`' "
  struct T { a: boolean, b: boolean }
  case T { a: true, b: false }
  when T { a: true, b: true }
    puts(1)
  when T { a: true, b: false }
    puts(2)
  when T { a: false, b: true }
    puts(3)
  end"
# destructuring
assert 'uncovered fields `value`' "
  struct T { value: int64 }
  case T { value: 123 }
  when T {}
    puts(0)
  else
    puts(1)
  end"
assert 'uncovered fields `a`, `b`' "
  struct T { a: int64, b: int64 }
  case T { a: 1, b: 2 }
  when T {}
    puts(0)
  else
    puts(2)
  end"
assert 'named field `value` is defined more than once' "
  struct T { value: int64 }
  case T { value: 123 }
  when T { value: a, value: b }
    puts(0)
  else
    puts(1)
  end"
# binding variables
assert 'identifier `x` is bound more than once in the same pattern' "
case (10, 20, 30)
when (x, x, z)
  puts(x + x + z)
end"
assert 'identifier `x` is bound more than once in the same pattern' "
struct S { a: int64, b: int64 }
case S { a: 10, b: 20 }
when S { a: x, b: x}
  puts(x + x + z)
end"
assert 'cannot find variable `_` in scope' "
_ = 1
puts(_)"
# type check
assert 'Semantic error: expected type `int64`, found `boolean`' "
def foo(n: int64)
  n
end
foo(true)"
assert 'Semantic error: expected type `(int64)`, found `int64`' "
def foo(t: (int64,))
  t
end
foo(100)"
assert 'Semantic error: expected type `A`, found `struct B { a: int64 }`' "
struct A { a: int64 }
struct B { a: int64 }
def foo(t: A)
  t
end
foo(B { a: 100 })"
assert 'Semantic error: expected type `(int64, int64)`, found `(int64, int64, int64)`' "
def foo(t: (int64, int64))
  case t
  when (1, 2, 3)
    puts(1)
  else
    puts(2)
  end
end
foo((1, 2))"
assert 'Semantic error: non-exhaustive pattern: `(int64::MIN..=0)`
Semantic error: non-exhaustive pattern: `(2..=int64::MAX)`' "case (1,)
when (1,)
  puts(1)
end"
# tuple
assert 'Semantic error: no field `3` on type `(int64, int64, int64)`' "(1, 2, 3).3"
assert 'Semantic error: no field `3` on type `(int64, int64, int64)`' "
x = (1, 2, 3)
x.3"
# struct
assert 'Semantic error: no field `b` on type `struct A { a: int64 }`' "
struct A { a: int64 }
a = A { a: 100 }
a.b"
# anonymous struct
assert 'expected type `{ a: int64, b: int64 }`, found `int64`' '
def foo(opts: { a: int64, b: int64 })
  opts.a + opts.b
end
foo(100)'