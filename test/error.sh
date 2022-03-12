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
assert 'cannot find variable `x` in scope' "a = x"
# undefined function
assert 'cannot find function `foo` in scope' "foo()"
# unreachable pattern
assert 'unreachable pattern: `1`' "
  def foo(n: int64)
    case n
    when 1
      puts(1)
    when 1
      puts(1)
    else
      puts(n)
    end
  end"
assert 'unreachable pattern: `false`' "
  case 5 > 3
  when true
    puts(true)
  when false
    puts(false)
  when false
    puts(0)
  end"
assert 'unreachable pattern: `"A"`' "
  case \"A\"
  when \"A\"
    puts(1)
  when \"A\"
    puts(2)
  else
    puts(3)
  end"
assert 'unreachable `else` clause' "
  case 5 > 3
  when true
    puts(true)
  when false
    puts(false)
  else
    puts(0)
  end"
assert 'unreachable pattern: `T { value: 0 }`' "
  struct T { value: int64 }
  t = T { value: 123 }
  case t
  when T { value: _ }
    puts(t)
  when T { value: 0 }
    puts(t)
  end"
assert 'unreachable pattern: `T { value: 0 }`' "
  struct T { value: int64 }
  t = T { value: 123 }
  case t
  when T { ... }
    puts(t)
  when T { value: 0 }
    puts(t)
  end"
assert 'unreachable pattern: `T { value: 0 }`' "
  struct T { value: int64 }
  t = T { value: 123 }
  case t
  when x
    puts(x)
  when T { value: 0 }
    puts(t)
  end"
assert 'unreachable pattern: `T { a: _, b: _ }`' "
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
assert 'unreachable `else` clause' 'case "hello"
when "hello"
  puts(1)
else
  puts(2)
end'
assert 'unreachable pattern: `0`' '
  def foo(n)
    case n
    when -9223372036854775808..=9223372036854775807
      puts(n)
    when 0
      puts(0)
    end
  end'
assert 'unreachable pattern: `0`' '
  def foo(n: int64 | string)
    case n
    when x: int64
      puts(x)
    when x: string
      puts(x)
    when 0
      puts(0)
    end
  end'
assert 'unreachable pattern: `{ a: _, b: _ }`' '
  case { a: 100, b: false }
  when { a: x, b: false } | { a: _, b: x }
    puts(x)
  end'
assert 'unreachable pattern: `{ a: _, b: _ }`' '
  struct T { value: int64 }
  case { a: T { value: 100 }, b: false }
  when { a: T { value: x }, b: false } | { a: _, b: x }
    puts(x)
  end'
# non-exhaustive pattern
assert 'non-exhaustive pattern: `int64::MIN..=0`' "
  def foo(n: int64)
    case n
    when 1
      puts(1)
    when 2
      puts(2)
    end
  end"
assert 'non-exhaustive pattern: `true`' "
  case 5 > 3
  when false
    puts(false)
  end"
assert 'non-exhaustive pattern: `false`' "
  case 5 > 3
  when true
    puts(true)
  end"
assert 'non-exhaustive pattern: `_: string`' '
  def foo(s: string)
    case s
    when "A"
      puts(1)
    when "B"
      puts(2)
    end
  end'
assert 'non-exhaustive pattern: `T { a: false, b: false }`' "
  struct T { a: boolean, b: boolean }
  case T { a: true, b: false }
  when T { a: true, b: true }
    puts(1)
  when T { a: true, b: false }
    puts(2)
  when T { a: false, b: true }
    puts(3)
  end"
assert 'non-exhaustive pattern: `_: string`' '
  def foo(): string
    "A"
  end
  case foo()
  when "A"
    puts(1)
  end'
assert 'non-exhaustive pattern: `_: string`' '
  def foo(value: string)
    case value
    when "A"
      puts(1)
    end
  end'
assert 'non-exhaustive pattern: `_: int64`' '
  def foo(a: string | int64)
    case a
    when x: string
      puts(x)
    end
  end'
assert 'non-exhaustive pattern: `_: int64`' '
  def foo(a: string | int64 | boolean)
    case a
    when x: string | boolean
      puts(x)
    end
  end'
assert 'non-exhaustive pattern: `_: int64`' '
  type U = string | int64 | boolean
  def foo(a: U)
    case a
    when x: string | boolean
      puts(x)
    end
  end'
assert 'non-exhaustive pattern: `_: int64`' '
  type U = string | int64
  def foo(a: U | boolean)
    case a
    when x: string | boolean
      puts(x)
    end
  end'
assert 'non-exhaustive pattern: `_: "unknown"`' '
  def foo(a: "ok" | "failed" | "unknown")
    case a
    when "ok"
      puts(1)
    when "failed"
      puts(2)
    end
  end'
assert 'non-exhaustive pattern: `_: "failed"`' '
  def foo(a: "ok" | "failed" | "unknown")
    case a
    when "ok" | "unknown"
      puts(1)
    end
  end'
assert 'non-exhaustive pattern: `_: false`' '
  def foo(a: false | true)
    case a
    when true
      puts(1)
    end
  end'
assert 'non-exhaustive pattern: `9223372036854775807`' '
  def foo(n)
    case n
    when -9223372036854775808..=9223372036854775806
      puts(n)
    end
  end'
assert 'non-exhaustive pattern: `9223372036854775807`' '
  def foo(n: int64 | boolean)
    case n
    when true | false
      puts(n)
    when -9223372036854775808..=9223372036854775806
      puts(n)
    end
  end'
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
assert 'unreachable pattern: `{ a: _, b: 3 }`' '
  def foo(t: { a: int64, b: int64 })
    case t
    when { a: _, ... } | { b: 3, ... }
      puts(0)
    else
      puts(1)
    end
  end'
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
assert 'variable `x` is not bound in all patterns' '
  case { a: 1, b: 2 }
  when { a: x, b: 0 } | { ... }
    puts(x)
  end'
assert 'variable `value` is not bound in all patterns' '
  struct T { value: int64 }
  case { a: T { value: 1 }, b: T { value: 2 } }
  when { a: T { value }, b: T { value: 0 } } | { a: _, b: _ }
    puts(x)
  end'
assert 'spread pattern can appear only once: `...`' '
  case { a: 100, b: 200, c: 300 }
  when { a, ..., ... }
    puts(a)
  end'
assert 'spread pattern can appear only once: `...y`' '
  case { a: 100, b: 200, c: 300 }
  when { a, ...x, ...y }
    puts(a)
  end'
assert 'spread pattern can appear only once: `...y`' '
  struct T { a: int64, b: int64, c: int64 }
  t = T { a: 100, b: 200, c: 300 }
  case t
  when T { a, ...x, ...y }
    puts(a)
  end'
assert 'spread pattern can appear only once: `...`' '
  struct T { a: int64, b: int64, c: int64 }
  t = T { a: 100, b: 200, c: 300 }
  case { t }
  when { t: T { ...x, ... } }
    puts(x)
  end'
# function - return type annotation
assert 'return type of function `bar()` is specified with `int64`, found `false`' '
  def bar(): int64
    false
  end'
assert 'return type of function `bar(int64)` is specified with `boolean`, found `int64`' '
  def bar(x: int64): boolean
    x + 1
  end'
# type check
assert 'expected type `int64`, found `true`' "
  def foo(n: int64)
    n
  end
  foo(true)"
assert 'expected type `(int64)`, found `int64`' "
  def baz(t: (int64,))
    t
  end
  def foo(n: int64)
    baz(n)
  end
  foo(100)"
assert 'expected type `A`, found `struct B { a: int64 }`' "
  struct A { a: int64 }
  struct B { a: int64 }
  def foo(t: A)
    t
  end
  foo(B { a: 100 })"
assert 'expected type `(int64, int64)`, found `(1, 2, 3)`' "
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
Semantic error: non-exhaustive pattern: `(2..=int64::MAX)`' "
  def foo(t: (int64,))
    case t
    when (1,)
      puts(1)
    end
  end"
assert 'expected type `1`, found `struct T { a: int64, b: boolean }`' '
  struct T { a: int64, b: boolean }
  case 1
  when T { a }
    puts(1)
  else
    puts(2)
  end'
# explict type annotated pattern
assert 'expected type `1`, found `2`' 'case 1
when x : 2
  puts(x)
end'
assert 'non-exhaustive pattern' '
n: int64 = 1
case n
when 1
  puts(n)
end'
# literal types
assert 'expected type `"A"`, found `"B"`' '
  case "A"
  when "A"
    puts(1)
  when "B"
    puts(2)
  end'
assert 'expected type `3`, found `1`' "
  case 3
  when 1
    puts(1)
  when 0..=2
    puts(2)
  else
    puts(3)
  end"
assert 'expected type `true`, found `false`' "
  case true
  when true
    puts(1)
  when false
    puts(2)
  end"
assert 'expected type `1`, found `2`' "
  case (1, 2, 3)
  when (2, 3, 4)
    puts(0)
  when (1, 2, 3)
    puts(1)
  else
    puts(2)
  end"
# tuple
assert 'no field `3` on type `(1, 2, 3)`' "(1, 2, 3).3"
assert 'no field `3` on type `(1, 2, 3)`' "
  x = (1, 2, 3)
  x.3"
# struct
assert 'no field `b` on type `struct A { a: int64 }`' "
  struct A { a: int64 }
  a = A { a: 100 }
  a.b"

# ---------------------------------
# Anonymous struct
# ---------------------------------
assert 'expected type `{ a: int64, b: int64 }`, found `100`' '
  def foo(opts: { a: int64, b: int64 })
    opts.a + opts.b
  end
  foo(100)'
assert 'identifier `a` is bound more than once in the same pattern' '
  case { a: 100, b: 200, c: 300 }
  when { a, ...a }
    puts(a)
  end'
# An alias of an anonymous structure cannot be initialized as a regular structure.
assert 'anonymous struct cannot be initialized with type alias `V1`' '
  type V1 = { value: int64 }
  puts(V1 { value: 100 })'
assert 'cannot find named field `a` in `{ value: int64 }`' '
  def foo(t: { value: int64 })
    case t
    when { value, a }
      puts(value)
    end
  end'
assert 'expected type `{ value: int64 }`, found `{ value: string }`' '
  def foo(t: { value: int64 })
    case t
    when { value } : { value: string }
      puts(value)
    end
  end'
# ---------------------------------
# Or-pattern
# ---------------------------------
assert 'expected type `struct T { a: int64 }`, found `{ a: 2 }`' '
  struct T { a: int64 }
  t = T { a: 0 }
  case t
  when T { a: 0 } | T { a: 1 } | { a: 2 }
    puts(0)
  else
    puts(1)
  end'