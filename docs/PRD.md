# PRD — Ratified

## The problem

A DRAT proof checker's whole value is that you can believe its `s VERIFIED`
without believing the solver that produced the proof. That belief rests on two
things: that the rules the checker applies are sound, and that the checker
applies them correctly.

The second is what tests attack, and [Refute](https://github.com/Leo-Y-Zhang/Refute)
attacks it hard — differential fuzzing against `drat-trim`, mutation-killed unit
tests, satisfiable-formula controls. The first is normally taken on trust from
the literature and restated in a design document in prose.

This project closes that half: it states the rules in Lean 4 and proves them,
so the argument is checked by a machine rather than read.

## Users

One reader, in three situations:

1. Someone deciding whether to trust a DRAT checker's output, who wants the rule
   itself pinned down rather than cited.
2. Someone reading `Refute` who reaches "that is the whole argument" in its design
   document and wants the argument.
3. Me, checking that the rule I implemented in Rust is the rule I think it is.

## Success criteria

- `checkProof_sound` is proved: an accepted proof implies unsatisfiability.
- `no_false_accept` is proved: no input refutes a satisfiable formula.
- The axiom list contains no `sorryAx` and no `Lean.ofReduceBool`, and the list is
  pinned so the build fails if that changes.
- Every load-bearing side condition has a recorded mutation that kills the build.
- No dependencies, so a reader can build it without fetching a library ten times
  the size of the proof.

All five hold. The evidence is in `README.md`, `MUTATIONS.md` and
`Ratified/Audit.lean`.

## Explicit non-goals

- **Verifying Refute.** The Rust is not extracted from this and this proves
  nothing about it. Saying otherwise would be the single most tempting overclaim
  available here, so it is stated as a non-goal and repeated in the README.
- **A parser.** Formulas and proofs arrive as Lean values.
- **An efficient checker.** Lists and linear scans throughout. The model is meant
  to be read, not run at scale.
- **Completeness.** Nothing claims every valid proof is accepted.
- **LRAT.** The hint-carrying format is a different check with different failure
  modes; RUP and RAT are the rules underneath both, and they are what is proved.

## Why there is no App Flow or Design Brief here

The standing process asks for four documents. Two of them describe a user moving
through an interface, and this artefact has no interface — it is a library whose
entire surface is a handful of definitions and theorems. Writing those two
documents would mean writing filler, so they are absent deliberately rather than
forgotten. The PRD and the TDD carry the content that applies.
