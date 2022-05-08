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
assert true "puts(true)"
assert false "puts(false)"
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
# struct which has string member
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
# struct which has union member
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
# number (range)
assert '2
1
2
3' "
  def foo(n)
    case n
    when 1
      puts(1)
    when 0..=2
      puts(2)
    else
      puts(3)
    end
  end
  foo(0)
  foo(1)
  foo(2)
  foo(3)"
assert '2
1
2
3' "
  def foo(n)
    m = case n
    when 1
      puts(1)
    when 0..=2
      puts(2)
    else
      puts(3)
    end
    m
  end
  foo(0)
  foo(1)
  foo(2)
  foo(3)"
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
  def foo(t: (boolean, int64))
    case t
    when (false, _)
      puts(0)
    when (true, x)
      puts(x)
    end
  end
  foo((true, 15))"
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
assert '100
200
300' '
  def foo(n: int64)
    case n
    when 1
      100
    when 2
      200
    else
      300
    end
  end
  puts(foo(1))
  puts(foo(2))
  puts(foo(3))'
assert 'n = 1
n = 2
3' '
  def foo(n: int64)
    case n < 3
    when true
      puts("n =", n)
      foo(n + 1)
    else
      n
    end
  end
  puts(foo(1))'
assert "{ a: 100 }
{ a: 55 }" '
  def foo(b: boolean)
    case b
    when true
      { a: 100 }
    when false
      { a: 55 } # widening to { a: int64 }
    end
  end
  puts(foo(true))
  puts(foo(false))'
assert "(100, \"foo\")
(200, \"baz\")" '
  def foo(b: boolean)
    case b
    when true
      (100, "foo")
    when false
      (200, "baz") # widening to (int64, string)
    end
  end
  puts(foo(true))
  puts(foo(false))'
assert '1000' '
  def foo(n)
    case n
    when -9223372036854775808..=9223372036854775807
      puts(n)
    end
  end
  foo(1000)'
# or-pattern
assert '0..=2
0..=2
3..<10
3..<10
10
11..' '
  def bar(n: int64)
    case n
    when 0 | 1 | 2
      "0..=2"
    when 3 | 4..<10
      "3..<10"
    when 10
      "10"
    else
      "11.."
    end
  end
  def baz(n: int64)
    puts(bar(n))
  end
  baz(0)
  baz(2)
  baz(3)
  baz(6)
  baz(10)
  baz(11)'
assert '100
200' '
  struct T { a: int64, b: int64 }
  def foo(t: T)
    case t
    when T { a: 1, b: a } | T { a, b: _ }
      a
    end
  end
  foo(T { a: 1, b: 100 }).puts()
  foo(T { a: 200, b: 100 }).puts()'
assert '100
200
3' '
  struct T { a: int64, b: int64 }
  
  def foo(t: { t: T })
    case t
    when { t: T { a, b: 1 } } | { t: T { a, b: 2 } }
      a
    when { t: T { a: _, b }}
      b
    end
  end
  { t: T { a: 100, b: 1 } }.foo().puts()
  { t: T { a: 200, b: 2 } }.foo().puts()
  { t: T { a: 300, b: 3 } }.foo().puts()'
assert '100
200
3' '
  struct T { a: int64, b: int64 }
  
  def foo(t: { t: T })
    case t
    when { t: T { a, b: 1 } | T { a, b: 2 } }
      a
    when { t: T { a: _, b }}
      b
    end
  end
  { t: T { a: 100, b: 1 } }.foo().puts()
  { t: T { a: 200, b: 2 } }.foo().puts()
  { t: T { a: 300, b: 3 } }.foo().puts()'
assert '1 100
1 200
2 100
2 200
3 300
3 400
3 300
3 400
4' '
  struct T { a: int64, b: (int64, int64) }
  def func(t: T)
    case t
    when T { a: 1, b: (x, _) }
      puts(1, x)
    when T { a: 2, b: (1 | 2, x) }
      puts(2, x)
    when T { a: 3 | 4, b: (1, x) | (x, 1) }
      puts(3, x)
    else
      puts(4)
    end
  end
  func(T { a: 1, b: (100, 200) })
  func(T { a: 1, b: (200, 100) })
  func(T { a: 2, b: (1, 100) })
  func(T { a: 2, b: (2, 200) })
  func(T { a: 3, b: (1, 300) })
  func(T { a: 3, b: (400, 1) })
  func(T { a: 4, b: (1, 300) })
  func(T { a: 4, b: (400, 1) })
  func(T { a: 2, b: (3, 0) })'

# ---------------------------------
# Explict type annotation
# ---------------------------------
assert '1000' '
  def foo(n: int64)
    case n
    when x: int64
      puts(x)
    end
  end
  foo(1000)'
# assert 'thousand
# 1000' '
#   def foo(n: int64)
#     case n
#     when x: 1000
#       puts("thousand")
#     when x: int64
#       puts(x)
#     end
#   end
#   foo(1000)
#   foo(1001)'
# literal types
assert '1' '
  case "A"
  when "A"
    puts(1)
  end'
assert '1' '
  case 100
  when 100
    puts(1)
  end'
assert '1' '
  case false
  when false
    puts(1)
  end'
assert '1' '
  def foo(v: "A")
    case v
    when "A"
      puts(1)
    end
  end
  foo("A")'
assert '100' '
  def foo(v: 1)
    case v
    when 1
      puts(100)
    end
  end
  foo(1)'
assert '100' '
  def foo(v: true)
    case v
    when true
      puts(100)
    end
  end
  foo(true)'
assert 'override 1
override 2
string C' '
  def baz(_: "A")
    puts("override 1")
  end
  def baz(_: "B")
    puts("override 2")
  end
  def baz(s: string)
    puts("string", s)
  end

  def foo(s: string)
    case s
    when "A"
      baz(s)
    when "B"
      baz(s)
    else
      baz(s)
    end
  end

  foo("A")
  foo("B")
  foo("C")'
assert 'override 1
override 2
int64 300' '
  def baz(_: 100)
    puts("override 1")
  end
  def baz(_: 200)
    puts("override 2")
  end
  def baz(n: int64)
    puts("int64", n)
  end

  def foo(n: int64)
    case n
    when 100
      baz(n)
    when 200
      baz(n)
    else
      baz(n)
    end
  end

  foo(100)
  foo(200)
  foo(300)'
assert 'override 1
override 2' '
  def baz(_: true)
    puts("override 1")
  end
  def baz(_: false)
    puts("override 2")
  end

  def foo(b: boolean)
    case b
    when true
      baz(b)
    when false
      baz(b)
    end
  end

  foo(true)
  foo(false)'
assert 'override 1
string B' '
  def baz(_: "A")
    puts("override 1")
  end
  def baz(s: string)
    puts("string", s)
  end

  def foo(t: (string, string))
    case t.0
    when "A"
      baz(t.0)
    else
      baz(t.1)
    end
  end

  foo(("A", "_"))
  foo(("_", "B"))'
assert 'override 1
string B' '
  struct T { name: string }
  def baz(_: "A")
    puts("override 1")
  end
  def baz(s: string)
    puts("string", s)
  end

  def foo(t: T)
    case t.name
    when "A"
      baz(t.name)
    else
      baz(t.name)
    end
  end

  foo(T {name: "A"})
  foo(T {name: "B"})'
assert 'override 1
string B' '
  def baz(_: "A")
    puts("override 1")
  end
  def baz(s: string)
    puts("string", s)
  end

  def foo(t: { values: (string, string) })
    case t.values.1
    when "A"
      baz(t.values.1)
    else
      baz(t.values.1)
    end
  end

  foo({ values: ("A", "A") })
  foo({ values: ("B", "B") })'
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
assert '1
2
3' '
  def greeting(_: "A")
    puts(1)
  end
  def greeting(_: "B")
    puts(2)
  end
  def greeting(_: string)
    puts(3)
  end
  greeting("A")
  greeting("B")
  greeting("C")'
assert 'Hello, English
こんにちは。 日本語
Sorry, I don'"'"'t speak Deutsch' '
  def greeting(lang: "English")
    puts("Hello,", lang)
  end
  def greeting(lang: "日本語")
    puts("こんにちは。", lang)
  end
  def greeting(lang: string)
    puts("Sorry, I don'"'"'t speak", lang)
  end

  greeting("English")
  greeting("日本語")
  greeting("Deutsch")'
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
  def foo(t: (int64, int64, int64))
    case t
    when (2, 3, 4)
      puts(0)
    when (1, 2, 3)
      puts(1)
    else
      puts(2)
    end
  end
  foo((1, 2, 3))"
assert "2" '
  def foo(t: (string, boolean, int64))
    case t
    when ("hello", false, 15)
      puts(1)
    when ("hello", true, 0..=15)
      puts(2)
    else
      puts(3)
    end
  end
  foo(("hello", true, 15))'
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
assert '1
2
3' '
  struct T { a: int64, b: int64, c: int64 }
  def foo(t: T)
    case t
    when T { a: 1, b: 2, ... }
      puts(1)
    when T { a: 1, c: 3, ... }
      puts(2)
    else
      puts(3)
    end
  end
  foo(T { a: 1, b: 2, c: 0})
  foo(T { a: 1, b: 3, c: 3})
  foo(T { a: 3, b: 3, c: 3})'
assert '100 200 300' '
  struct T { a: int64, b: int64, c: int64 }
  case T { a: 100, b: 200, c: 300 }
  when T { a, ...x }
    puts(a, x.b, x.c)
  end'
assert '1 3' '
  struct T { a: int64, b: int64, c: int64 }
  t1 = T { a: 1, b: 2, c: 3 }
  T { a, ...x } = t1
  puts(a, x.c)'
assert 'T { a: 50, b: 10, c: 40 }' '
  struct T {
    a: int64,
    b: int64,
    c: int64,
  }
  t1 = T { a: 1, b: 2, c: 3 }
  t2 = T { ...t1, a: 3, b: 10 } # { a: 3, b: 10, c: 3 }
  t3 = T { ...t1, ...t2, ...{ a: 50, c: 40 } }
  puts(t3)'

# ---------------------------------
# Anonymous struct
# ---------------------------------
assert '{ a: 1 }' 'puts({a: 1})'
assert '{ b: true, m: "hello" }' 'puts({m: "hello", b: true})'
assert '{ t: { a: 123 }, z: 33 }' '
  t1 = { a: 123 }
  t2 = { t: t1, z: 33}
  puts(t2)'
assert '6
9' '
  def foo(n: int64, options: { repeat: boolean, count: int64 })
    case options.repeat
    when true
      options.count * n
    else
      n
    end
  end
  6.foo({ count: 0, repeat: false }).puts()
  3.foo({ count: 3, repeat: true }).puts()'
assert '123' '
  def foo({ a, ... }: { a: int64 })
    a
  end
  { a: 123 }.foo().puts()'
assert '{ a: 100, b: 200, c: 300 }' '
  t1 = { a: 100, b: 200 }
  t2 = { c: 300, ...t1 }
  puts(t2)'
assert 'T { a: 100, b: 200, c: 400 }' '
  struct T { a: int64, b: int64, c: int64, }
  t1 = T { a: 100, b: 200, c: 300 }
  t2 = T { ...t1, c: 400 }
  puts(t2)'
assert 'T { a: 0, b: 1, c: 400 }' '
  struct T { a: int64, b: int64, c: int64, }
  t1 = T { a: 100, b: 200, c: 300 }
  t2 = T { ...t1, c: 400 }
  t3 = T { ...t1, ...t2, a: 0, b: 1 }
  puts(t3)'
assert '100' '
  case { a: 100, b: 200 }
  when { a, ... }
    puts(a)
  end'
assert '100 300' '
  case { a: 100, b: 200, c: 300 }
  when { a, ...x }
    puts(a, x.c)
  end'

# ---------------------------------
# Type aliases
# ---------------------------------
assert '101' '
  type K = int64
  n: K = 101
  puts(n)'
assert 'x value is 136
y value is 353' '
  type Point = {
    x: int64,
    y: int64,
  }
  def printCoord(pt: Point)
    puts("x value is", pt.x)
    puts("y value is", pt.y)
  end
  printCoord({ x: 136, y: 353 })'
assert '900 800' '
  type K = int64
  type T = (K, K)
  type S = { pair: T }
  def kts(s: S)
    case s
    when x: S
      puts(x.pair.0, x.pair.1)
    end
  end
  kts({ pair: (900, 800) })'
# We can initialze a regular struct from type alias.
assert 'T { value: 100 }' '
  struct T { value: int64 }
  type V1 = T
  puts(V1 { value: 100 })'
# The anonymous struct pattern must match a type alias.
assert '100 200' '
  type T = { value: string }
  def foo(n: (int64, T))
    case n
    when (x: int64, { value })
      puts(x, value)
    end
  end
  foo((100, { value: "200" }))'

# ---------------------------------
# Union type
# ---------------------------------
assert '1234567
abcdefg' '
  type ID = string | int64
  def printID(id: ID)
    puts(id)
  end
  printID(1234567)
  printID("abcdefg")'
assert '1234567
abcdefg' '
  type ID = string | int64
  def printID(id: ID)
    puts(id)
  end
  x = 1234567
  printID(x)
  y = "abcdefg"
  printID(y)'
assert 'a = 102030
b = true' '
  type Field = (string, int64 | boolean)
  def print_field(t: Field)
    puts(t.0, "=", t.1)
  end
  print_field(("a", 102030))
  t = ("b", true)
  print_field(t)'
assert 'a = true
b = false
c = on
d = off' '
  struct Option {
    name: string,
    value: boolean | "on" | "off",
  }
  def show_option(opt: Option)
    puts(opt.name, "=", opt.value)
  end
  show_option(Option { name: "a", value: true })
  show_option(Option { name: "b", value: false })
  show_option(Option { name: "c", value: "on" })
  opt = Option { name: "d", value: "off" }
  show_option(opt)'
assert 'a = true
b = false
c = on
d = off' '
  def show_option(opt: { name: string, value: boolean | "on" | "off" })
    puts(opt.name, "=", opt.value)
  end
  show_option({ name: "a", value: true })
  fv = { value: false }
  show_option({ name: "b", ...fv })
  opt1 = { name: "c", value: "on" }
  show_option(opt1)
  off = { value: "off" }
  opt2 = { name: "d", ...off }
  show_option(opt2)'
assert '105' '
  a: int64 | string = 105
  puts(a)'
assert 'false true' '
  def foo(n): int64 | boolean
    n > 0
  end
  puts(foo(0), foo(1))'
assert 'ok
error' '
  type U = "ok" | "error"
  def foo(b: string | int64)
    puts(b)
  end
  def bar(b: U | "failed")
    puts(b)
  end
  a: U = "ok"
  b: U = "error"
  foo(a)
  bar(b)'
assert 'hundred
TRUE' '
  struct T1 { name: string, value: int64 }
  struct T2 { name: string, value: boolean }
  def print_name(t: T1 | T2)
    puts(t.name)
  end
  print_name(T1 { name: "hundred", value: 100 })
  print_name(T2 { name: "TRUE", value: true })'
assert '100
hundred
TRUE' '
  struct T1 { name: string | int64, value: int64 }
  struct T2 { name: string, value: boolean }
  struct T3 { value: T1 | T2 }
  def print_name(t: T3)
    puts(t.value.name)
  end
  print_name(T3 { value: T1 { name: 100, value: 200 }})
  print_name(T3 { value: T1 { name: "hundred", value: 300 }})
  print_name(T3 { value: T2 { name: "TRUE", value: true }})'
assert '20
30
40
50
true' '
  type S = string | boolean
  type V1 = { value: int64 }
  type V2 = { value: string }
  type V3 = { value: S }
  type T =
    (int64, V1) |
    (int64, V1, int64) |
    (int64, V2) |
    (int64, V3, int64)
  def print_2nd(t: T)
    puts(t.1.value)
  end
  print_2nd((10, { value: 20 }))
  print_2nd((20, { value: 30 }, 40))
  print_2nd((30, { value: "40" }))
  print_2nd((40, { value: "50" }, 50))
  print_2nd((50, { value: true }, 50))'
assert 'abc
12345' '
  def foo(a: string | int64)
    case a
    when x: int64 | string
      puts(x)
    end
  end
  foo("abc")
  foo(12345)'
assert 'abc
12345' '
  def foo(a: string | int64)
    case a
    when x: string
      puts(x)
    when x: int64
      puts(x)
    end
  end
  foo("abc")
  foo(12345)'
assert 'abc
12345
false' '
  type U = string | int64
  def foo(a: U | boolean)
    case a
    when x: string | boolean | int64
      puts(x)
    end
  end
  foo("abc")
  foo(12345)
  foo(false)'
assert '1
2
3' '
  def foo(a: "ok" | "failed" | "unknown")
    case a
    when "ok"
      puts(1)
    when "failed"
      puts(2)
    when "unknown"
      puts(3)
    end
  end
  foo("ok")
  foo("failed")
  foo("unknown")'
assert '1
2
2' '
  def foo(a: "ok" | "failed" | "unknown")
    case a
    when "ok"
      puts(1)
    when "failed" | "unknown"
      puts(2)
    end
  end
  foo("ok")
  foo("failed")
  foo("unknown")'
assert '1
2' '
  def foo(a: true | false)
    case a
    when true
      puts(1)
    when false
      puts(2)
    end
  end
  foo(true)
  foo(false)'
assert 'true
false' '
  def foo(a: true | false)
    case a
    when false | true
      puts(a)
    end
  end
  foo(true)
  foo(false)'
assert '1
2
3
4
5' '
  def foo(a: boolean | "ok" | "failed" | "unknown")
    case a
    when "ok"
      puts(1)
    when "failed"
      puts(2)
    when "unknown"
      puts(3)
    when true
      puts(4)
    when false
      puts(5)
    end
  end
  foo("ok")
  foo("failed")
  foo("unknown")
  foo(true)
  foo(false)'
assert 'true
INT_MIN
1000' '
  def foo(n: int64 | boolean)
    case n
    when x: boolean
      puts(x)
    when -9223372036854775807..=9223372036854775807
      puts(n)
    when -9223372036854775808
      puts("INT_MIN")
    end
  end
  foo(true)
  foo(-9223372036854775808)
  foo(1000)'
# Pattern matching for union type which has a tuple/struct
assert '100 200
0' '
  type S = string | boolean
  type V1 = { value: int64 }
  type V2 = { value: string }
  type V3 = { value: S }
  type T =
    (int64, V1) |
    (int64, V1, int64) |
    (int64, V2) |
    (int64, V3, int64)
  def foo(t: T)
    case t
    when (x: int64, { value })
      puts(x, value)
    else
      puts(0)
    end
  end
  foo((100, { value: 200 }))
  foo((100, { value: 200 }, 300))'
assert '102030
chocolate' '
  type A = int64
  type B = string
  def foo(n: A | B)
    case n
    when a: A
      puts(a)
    when b: B
      puts(b)
    end
  end
  foo(102030)
  foo("chocolate")'
assert '203040
cookie' '
  type A = int64
  type B = string
  def foo(n: A | B)
    case n
    when x: A | B
      puts(x)
    end
  end
  foo(203040)
  foo("cookie")'
# You can annotate patterns in an or-pattern with parentheses.
assert '304050
candy' '
  type A = int64
  type B = string
  def foo(n: A | B)
    case n
    when (x: A) | (x: B)
      puts(x)
    end
  end
  foo(304050)
  foo("candy")'
# or-pattern contains more than one complex type.
assert '405060
ice cream' '
  struct T1 { value: int64 }
  struct T2 { value: string }
  def foo(t: T1 | T2)
    case t
    when T1 { value } | T2 { value }
      puts(value)
    end
  end
  foo(T1 { value: 405060 })
  foo(T2 { value: "ice cream" })'
assert '1 two
three 4' '
  type T1 = (int64, string)
  type T2 = (string, int64)
  def foo(t: T1 | T2)
    case t
    when (x: int64, y: string)
      puts(x, y)
    when (x: string, y: int64)
      puts(x, y)
    end
  end
  foo((1, "two"))
  foo(("three", 4))'
assert '1 two
three 4' '
  type T1 = (int64, string)
  type T2 = (string, int64)
  def foo(t: T1 | T2)
    case t
    when (x: int64, y: string) | (x: string, y: int64)
      puts(x, y)
    end
  end
  foo((1, "two"))
  foo(("three", 4))'
assert 'T1 1 two
T2 three 4' '
  type T1 = (int64, string)
  type T2 = (string, int64)
  def foo(t: T1 | T2)
    case t
    when (x: int64, y: string)
      puts("T1", x, y)
    when (x: string, y: int64)
      puts("T2", x, y)
    end
  end
  foo((1, "two"))
  foo(("three", 4))'
assert '1 two
three 4' '
  type T1 = (int64, string)
  type T2 = (string, int64)
  def foo(t: T1 | T2)
    case t
    when ((x, y): T1) | ((x, y): T2)
      puts(x, y)
    end
  end
  foo((1, "two"))
  foo(("three", 4))'
assert 'T1 1 two
T2 three 4' '
  type T1 = (int64, string)
  type T2 = (string, int64)
  def foo(t: T1 | T2)
    case t
    when ((x, y): T1)
      puts("T1", x, y)
    when ((x, y): T2)
      puts("T2", x, y)
    end
  end
  foo((1, "two"))
  foo(("three", 4))'
assert '(1, 2)
("one", 2)
(1, 2)
("one", 2)' '
  type T = (int64, int64) | (string, int64)
  type U = (int64 | string, int64)

  t1: T = (1, 2)
  t2: T = ("one", 2)
  u1: U = t1
  u2: U = t2
  puts(t1)
  puts(t2)
  puts(u1)
  puts(u2)'
# Union type pattern match
assert '1
2' '
def foo(n: 1 | 2)
  case n
  when 1
    puts(1)
  when 2
    puts(2)
  end
end
foo(1)
foo(2)'
assert '1
2' '
def foo(n: 1 | 2)
  case n
  when x: 1
    puts(x)
  when x: 2
    puts(x)
  end
end
foo(1)
foo(2)'
assert '1
2' '
def foo(n: 1 | 2)
  case n
  when x
    puts(x)
  end
end
foo(1)
foo(2)'
assert '1
2' '
def foo(n: 1 | 2)
  case n
  when x: int64
    puts(x)
  end
end
foo(1)
foo(2)'
assert '1
2' '
def foo(n: 1 | 2)
  case n
  when x: 1 | 2
    puts(x)
  end
end
foo(1)
foo(2)'
assert '1
2' '
def foo(n: 1 | 2)
  case n
  when 1 | 2
    puts(n)
  end
end
foo(1)
foo(2)'
assert '1 2
three 4' '
  type T = (int64, int64) | (string, int64)
  type U = (int64 | string, int64)
  def foo(t: U)
    case t
    when x: T
      puts(x.0, x.1)
    end
  end
  foo((1, 2))
  foo(("three", 4))'
# union type in tuple
assert "1
two" 'def foo(n: (int64 | string,))
  case n
  when (x,)
    puts(x)
  end
end
foo((1,))
foo(("two",))'
# variable pattern captures every product of union member types.
assert '1 two
three 4' '
  def foo(n: (int64, string) | (string, int64))
    case n
    when (x: int64 | string, y: string | int64)
      puts(x, y)
    end
  end
  foo((1, "two"))
  foo(("three", 4))'
assert '1 two
three 4' '
  def foo(n: (int64, string) | (string, int64))
    case n
    when (x, y): (int64 | string, string | int64)
      puts(x, y)
    end
  end
  foo((1, "two"))
  foo(("three", 4))'
# variable/wildcard pattern consumes multiple choice in nested union
assert '1 100
true three' '
  type U = (int64 | boolean, int64 | string)
  def foo(t: U)
    case t
    when (x, y)
      puts(x, y)
    end
  end
  foo((1, 100))
  foo((true, "three"))'
assert '1 100
true three' '
  type U1 = (int64, int64)
  type U2 = (boolean, string)
  def foo(t: U1 | U2)
    case t
    when (x, y)
      puts(x, y)
    end
  end
  foo((1, 100))
  foo((true, "three"))'
assert '1 100
one 101
2 two
true three' '
  type U1 = (int64 | string, int64)
  type U2 = (int64 | boolean, string)
  def foo(t: U1 | U2)
    case t
    when (x, y)
      puts(x, y)
    end
  end
  foo((1, 100))
  foo(("one", 101))
  foo((2, "two"))
  foo((true, "three"))'
assert '1 3
2 3
3 5
4 5' '
  type U1 = (1 | 2, 3)
  type U2 = (3 | 4, 5)
  def foo(t: U1 | U2)
    case t
    when (x, y)
      puts(x, y)
    end
  end
  foo((1, 3))
  foo((2, 3))
  foo((3, 5))
  foo((4, 5))'
assert '1 3
2 3
1 4
2 4' '
  type U1 = (1 | 2, 3)
  type U2 = (1 | 2, 4)
  def foo(t: U1 | U2)
    case t
    when (x, y)
      puts(x, y)
    end
  end
  foo((1, 3))
  foo((2, 3))
  foo((1, 4))
  foo((2, 4))'
assert 'T1 { value: 1 } T2 { value: "two" }
T2 { value: "three" } T1 { value: 4 }' '
  struct T1 { value: int64 }
  struct T2 { value: string }
  type U1 = (T1, T2)
  type U2 = (T2, T1)
  def foo(u: U1 | U2)
    case u
    when (x, y)
      puts(x, y)
    end
  end
  foo((T1 { value: 1 }, T2 { value: "two" }))
  foo((T2 { value: "three" }, T1 { value: 4 }))'
assert '1
two' '
  def foo(t: { value: int64 } | { value: string })
    case t
    when { value }
      puts(value)
    end
  end
  foo({ value: 1 })
  foo({ value: "two" })'
# or-pattern contains slightly different patterns.
assert '1 2
three 4
5 six
seven eight' '
  struct T1 { value: int64 }
  struct T2 { value: string }
  # type T3 = (T1 | T2, int64)
  # type T4 = (T1 | T2, string)
  # `T3 | T4` => (T1 | T2, int64 | string)
  def foo(t: (T1 | T2, int64 | string))
    case t
    when (T1 { value } | T2 { value }, x)
      puts(value, x)
    end
  end
  foo((T1 { value: 1 }, 2))
  foo((T2 { value: "three" }, 4))
  foo((T1 { value: 5 }, "six"))
  foo((T2 { value: "seven" }, "eight"))'
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
# narrowing
assert 'integer is 1000
string is hello' '
  def bar(n: int64)
    puts("integer is", n)
  end
  def bar(s: string)
    puts("string is", s)
  end
  def foo(v: int64 | string)
    case v
    when x: int64
      bar(x)
    when x: string
      bar(x)
    end
  end

  foo(1000)
  foo("hello")'
# The return type of a function which can return multiple literal values.
assert 'one
zero' '
  def to_int(b: boolean)
    case b
    when true
      1
    when false
      0
    end
  end
  def zero_or_one(n: 0 | 1)
    case n
    when 0
      puts("zero")
    when 1
      puts("one")
    end
  end

  true.to_int().zero_or_one()
  false.to_int().zero_or_one()'

# examples
assert 13 "$(cat examples/foo.paty)"
assert 55 "$(cat examples/fib.paty)"

echo OK