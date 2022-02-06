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
assert "33
44" "_ = puts(33)
puts(44)"
assert "66" "(x, y, z) = (11, 22, 33)
puts(x + y + z)"
assert "231" "((a, b, c), (d, e), (f,)) = ((11, 22, 33), (44, 55), (66,))
puts(a + b + c + d + e + f)"
# function
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
assert '1' "
case 102030
when _
  puts(1)
end"
assert '102030' "
case 102030
when x
  puts(x)
end"
assert '15' "
case (true, 15)
when (false, _)
  puts(0)
when (true, x)
  puts(x)
end"
assert '60' "
case (10, 20, 30)
when (x, y, z)
  puts(x + y + z)
end"
assert '33
66
100' '
def foo(n)
  puts(n)
  n * 2
end
x = foo(33)
puts(x)
puts(x + 34)'
assert "100
55" '
def foo(b: boolean)
  case b
  when true
    100
  when false
    55
  end
end
puts(foo(true))
puts(foo(false))'
# function overloading
assert "30
true
hello" '
def foo(n: int64)
  puts(n)
end
def foo(b: boolean)
  puts(b)
end
def foo(s: string)
  puts(s)
end
foo(30)
foo(true)
foo("hello")'
assert '100 baz!' '
def baz(n: int64, t: (boolean, string))
  puts(baz(n), baz(t))
end
def baz(n: int64)
  n * 10
end
def baz(t: (boolean, string))
  case t
  when (_, s)
    s
  end
end
baz(10, (true, "baz!"))'
# uniform function call syntax
assert 'hi' '"hi".puts()'
assert '100 baz!' '
def square(n)
  n * n
end
def baz(n, message: string)
  n.puts(message)
end
10.square().baz("baz!")'
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
# tuple
assert "2022 1 22" "
date = (2022, 1, 22)
puts(date.0, date.1, date.2)"
assert "30 false 110 true" "
def add_and_moreThan100(t: (int64, int64))
  (t.0 + t.1, t.0 + t.1 > 100)
end
t1 = add_and_moreThan100((10, 20))
t2 = add_and_moreThan100((90, 20))
puts(t1.0, t1.1, t2.0, t2.1)"
assert "(1, 2, 3)" "puts((1, 2, 3))"
assert "1" "
case (1, 2, 3)
when (2, 3, 4)
  puts(0)
when (1, 2, 3)
  puts(1)
else
  puts(2)
end"
assert "2" '
case ("hello", true, 15)
when ("hello", false, 15)
  puts(1)
when ("hello", true, 0..=15)
  puts(2)
else
  puts(3)
end'
# zero-sized struct/tuple
assert "()" "
a = ()
puts(a)"
assert "A {}" "
struct A {}
a = A {}
puts(a)"
assert '((), E {})' '
struct E {}
def foo(t: (), s: E)
  (t, s)
end
puts(foo((), E {}))'
assert 'WeAreZst { one: Zst {}, two: Zst {} }
(Zst {})' '
struct Zst {}
struct WeAreZst {
  one: Zst,
  two: Zst,
}
def printZst()
  puts(WeAreZst { one: Zst {}, two: Zst {} })
end
_ = printZst()
puts((Zst {},))'
# struct
assert "C { b: B { a: 50 }, c: (A {}, B { a: 60 }) }" '
struct A {}
struct B { a: int64 }
struct C { b: B, c: (A, B), }
c = C { b: B { a: 50 }, c: (A {}, B { a: 60 })}
puts(c)'
assert "C { b: B { a: 88 }, c: (A {}, B { a: 99 }) }" '
struct C { b: B, c: (A, B), }
struct B { a: int64 }
struct A {}
a = A {}
b = B { a: 88 }
c = C { b: b, c: (A {}, B { a: 33*3 })}
puts(c)'
assert 'Year 2022' '
struct D { foo: int64, bar: boolean, baz: string }
d = D { bar: true, foo: 2022, baz: "Year" }
D { bar: x, foo: y, baz: z} = d
case D { bar: x, foo: y, baz: z }
when D { bar: false, ... }
  puts(false)
when D { foo: foo, baz, ... }
  puts(baz, foo)
end'
assert 'Year 2022' '
struct D { foo: int64, bar: boolean, baz: string }
d = D { bar: true, foo: 2022, baz: "Year" }
puts(d.baz, d.foo)'
assert '3' '
struct D { foo: int64, bar: boolean, baz: string }
d = D { bar: false, foo: 1000, baz: "Hello" }
case d
when D { bar: true, ... }
  puts(1)
when D { foo: 999, ... }
  puts(2)
when D { baz: "Hello", ... }
  puts(3)
else
  puts(4)
end'
assert 'Year 2022' '
struct D { foo: int64, bar: boolean, baz: string }
d = D { bar: true, foo: 2022, baz: "Year" }
D { bar: _, ... } = d
D { foo, ... } = d
D { baz, ... } = d
puts(baz, foo)'
# anonymous struct
assert '{ a: 1 }' 'puts({a: 1})'
assert '{ b: true, m: "hello" }' 'puts({m: "hello", b: true})'
assert '{ t: { a: 123 }, z: 33 }' '
t1 = { a: 123 }
t2 = { t: t1, z: 33}
puts(t2)'
# examples
assert 13 "$(cat examples/foo.paty)"
assert 55 "$(cat examples/fib.paty)"

echo OK