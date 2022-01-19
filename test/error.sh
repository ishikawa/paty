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
