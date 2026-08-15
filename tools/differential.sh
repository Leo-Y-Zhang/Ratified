#!/bin/sh
# Run this development's checker and an independent implementation over the same
# formula/proof pairs and compare verdicts.
#
# The independent implementation is Refute (https://github.com/Leo-Y-Zhang/Refute),
# a DRAT checker written in Rust to the same rule. Nothing links the two beyond
# that rule -- no shared code, no extraction -- so agreement is evidence about the
# rule's statement, not a tautology.
#
#   tools/differential.sh <ratified-binary> <refute-binary> <fixture-dir>
#
# Exit 0 when every pair agrees.

set -eu

RATIFIED=${1:?usage: differential.sh <ratified-binary> <refute-binary> <fixture-dir>}
REFUTE=${2:?usage: differential.sh <ratified-binary> <refute-binary> <fixture-dir>}
FIXTURES=${3:?usage: differential.sh <ratified-binary> <refute-binary> <fixture-dir>}

verdict() {
  # Normalise to VERIFIED / NOT-VERIFIED / ERROR by exit code, so the two tools
  # are compared on their answer and not on their wording.
  set +e
  "$@" >/dev/null 2>&1
  code=$?
  set -e
  case "$code" in
    0) echo "VERIFIED" ;;
    1) echo "NOT-VERIFIED" ;;
    *) echo "ERROR($code)" ;;
  esac
}

agree=0
disagree=0

printf '%-42s %-14s %-14s %s\n' FIXTURE RATIFIED REFUTE RESULT
printf '%-42s %-14s %-14s %s\n' ------- -------- ------ ------

for proof in "$FIXTURES"/*.drat; do
  [ -e "$proof" ] || continue
  base=${proof%.drat}
  cnf="$base.cnf"
  [ -f "$cnf" ] || continue
  name=$(basename "$base")

  a=$(verdict "$RATIFIED" "$cnf" "$proof")
  b=$(verdict "$REFUTE" "$cnf" "$proof" --drat)

  if [ "$a" = "$b" ]; then
    agree=$((agree + 1))
    result=agree
  else
    disagree=$((disagree + 1))
    result=DISAGREE
  fi
  printf '%-42s %-14s %-14s %s\n' "$name" "$a" "$b" "$result"
done

echo
echo "$agree agreed, $disagree disagreed"
[ "$disagree" -eq 0 ]
