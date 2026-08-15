/-
DIMACS and DRAT readers.

**Nothing in this file is verified.** It is the boundary of the development: the
theorems in the other modules are about `checkProof` applied to Lean values, and
this is what turns bytes into those values. A bug here is a bug no theorem in
this repository excludes, which is why the readers fail loudly rather than
skipping what they cannot understand — a reader that silently dropped a
malformed clause would make the verdict meaningless while still printing it.

The proved part starts the moment `parseCnf` and `parseDrat` return.
-/
import Ratified.Proof

namespace Ratified.Parse

open Ratified

/-- DIMACS numbering: positive is the variable, negative its complement. Zero is
the terminator and never reaches here. -/
def litOfInt (i : Int) : Lit := ⟨i.natAbs, decide (0 < i)⟩

/-- Split on whitespace, dropping empties. Written out rather than taken from the
string library so that the reader does not move under a toolchain bump; it also
means `\r` from a CRLF file is dropped like any other whitespace. -/
private def splitTokens : List Char → List Char → List String → List String
  | [], current, acc =>
      (if current.isEmpty then acc else String.ofList current.reverse :: acc).reverse
  | c :: rest, current, acc =>
      if c.isWhitespace then
        splitTokens rest [] (if current.isEmpty then acc else String.ofList current.reverse :: acc)
      else
        splitTokens rest (c :: current) acc

private def tokensOf (line : String) : List String := splitTokens line.toList [] []

/-- A DIMACS comment (`c ...`) or the header (`p cnf ...`). Literal tokens begin
with a digit or a minus sign, so testing the first character is enough. -/
private def isCommentToken (tok : String) : Bool := tok.front == 'c' || tok.front == 'p'

/-- Read a DIMACS CNF formula.

Comment and header lines are skipped; everything else is a stream of integers
with `0` ending each clause, so a clause may span lines. An unterminated final
clause is an error, not a clause. -/
def parseCnf (text : String) : Except String Formula := do
  let mut clauses : Array Clause := #[]
  let mut current : Array Lit := #[]
  let mut lineNo := 0
  for rawLine in text.splitOn "\n" do
    lineNo := lineNo + 1
    let toks := tokensOf rawLine
    if toks.head?.any isCommentToken then
      continue
    for tok in toks do
      match tok.toInt? with
      | none => throw s!"line {lineNo}: not an integer: {tok}"
      | some 0 =>
          clauses := clauses.push current.toList
          current := #[]
      | some i => current := current.push (litOfInt i)
  if !current.isEmpty then
    throw "formula ends with a clause that is not terminated by 0"
  return clauses.toList

/-- Read a DRAT proof.

One step per line, which is what solvers and `drat-trim` write. A leading `d`
makes the line a deletion. Every line must be terminated by `0`; a bare `0` is
the addition of the empty clause, which is how a refutation ends. -/
def parseDrat (text : String) : Except String (List Step) := do
  let mut steps : Array Step := #[]
  let mut lineNo := 0
  for rawLine in text.splitOn "\n" do
    lineNo := lineNo + 1
    let toks := tokensOf rawLine
    if toks.isEmpty || toks.head?.any (fun t => t.front == 'c') then
      continue
    let isDeletion := toks.head? == some "d"
    let body := if isDeletion then toks.drop 1 else toks
    let mut lits : Array Lit := #[]
    let mut terminated := false
    for tok in body do
      match tok.toInt? with
      | none => throw s!"line {lineNo}: not an integer: {tok}"
      | some 0 => terminated := true
      | some i => lits := lits.push (litOfInt i)
    if !terminated then
      throw s!"line {lineNo}: step is not terminated by 0"
    steps := steps.push (if isDeletion then .del lits.toList else .add lits.toList)
  return steps.toList

end Ratified.Parse
