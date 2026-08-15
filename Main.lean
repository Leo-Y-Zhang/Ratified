/-
The command line.

    ratified <formula.cnf> <proof.drat>

Reads the pair, hands them to `Ratified.checkProof`, and reports the verdict.
The function it calls is the one `checkProof_sound` is about, so a `s VERIFIED`
here means the formula has no model -- subject to the two things the theorem does
not cover and this file does: the readers in `Ratified.Parse`, and the fact that
a compiled binary is produced by Lean's compiler rather than reduced by its
kernel. The kernel-checked version of the same claim, for formulas small enough
to decide that way, is in `Ratified.Examples`.

Exit codes follow the usual convention for this kind of tool: 0 verified,
1 not verified, 2 could not read the input.
-/
import Ratified
import Ratified.Parse

open Ratified

def usage : String :=
  "usage: ratified <formula.cnf> <proof.drat>\n\
   \n\
   Checks a DRAT proof against a DIMACS formula using the rule proved sound in\n\
   this development. Exit 0 verified, 1 not verified, 2 unreadable input."

def main (args : List String) : IO UInt32 := do
  match args with
  | [cnfPath, proofPath] =>
      let cnfText ← IO.FS.readFile cnfPath
      let proofText ← IO.FS.readFile proofPath
      match Parse.parseCnf cnfText with
      | .error e =>
          IO.eprintln s!"formula: {e}"
          return 2
      | .ok formula =>
        match Parse.parseDrat proofText with
        | .error e =>
            IO.eprintln s!"proof: {e}"
            return 2
        | .ok steps =>
            if checkProof formula steps then
              IO.println "s VERIFIED"
              return 0
            else
              IO.println "s NOT VERIFIED"
              return 1
  | _ =>
      IO.eprintln usage
      return 2
