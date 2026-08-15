#!/bin/sh
# Run the checker over the fixture corpus and compare every verdict with
# fixtures/EXPECTED.
#
#   tools/fixtures.sh [binary] [fixture-dir]
#
# Exit 0 when every verdict matches.

set -eu

BIN=${1:-.lake/build/bin/ratified}
DIR=${2:-fixtures}

pass=0
fail=0

printf '%-42s %-14s %-14s %s\n' FIXTURE EXPECTED GOT RESULT
printf '%-42s %-14s %-14s %s\n' ------- -------- --- ------

# Read the manifest up front: the loop runs a binary each iteration and should
# not be sharing its standard input with one.
manifest=$(grep -v '^[[:space:]]*#' "$DIR/EXPECTED" | grep -v '^[[:space:]]*$')

echo "$manifest" | while IFS=' ' read -r expected name rest; do
  [ -n "${name:-}" ] || continue
  set +e
  "$BIN" "$DIR/$name.cnf" "$DIR/$name.drat" >/dev/null 2>&1 </dev/null
  code=$?
  set -e
  case "$code" in
    0) got=VERIFIED ;;
    1) got=NOT-VERIFIED ;;
    *) got="ERROR($code)" ;;
  esac
  if [ "$got" = "$expected" ]; then
    result=ok
  else
    result=FAIL
  fi
  printf '%-42s %-14s %-14s %s\n' "$name" "$expected" "$got" "$result"
  [ "$result" = ok ] || echo FAILED >> "$DIR/.failures"
done

if [ -f "$DIR/.failures" ]; then
  fail=$(wc -l < "$DIR/.failures")
  rm -f "$DIR/.failures"
  echo
  echo "$fail fixture(s) gave the wrong verdict"
  exit 1
fi

pass=$(echo "$manifest" | wc -l)
echo
echo "$pass fixtures, every verdict as expected"
