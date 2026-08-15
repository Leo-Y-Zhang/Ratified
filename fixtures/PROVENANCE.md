# Where these came from

Nine formula/proof pairs, carried here from the test corpus of
[Refute](https://github.com/Leo-Y-Zhang/Refute) (MIT, same author). None of them
was written for this repository, which is the point: they exercise the checker
against proofs produced by a solver rather than by the person proving the rule
sound.

No file here contains a comment line, so nothing about the machine that produced
them travels with them.

## The positives

| Fixture | What it is |
| --- | --- |
| `tiny_unsat` | Three clauses over two variables. Small enough to follow by hand. |
| `empty_clause_in_cnf` | The formula already contains the empty clause; the proof is the single line `0`. |
| `deletes_originals` | Exercises deletion of clauses that came from the formula rather than the proof. |
| `real_rat_proof` | 91 additions, 20 of them RAT. The fixture no generator produces — its lemma is RAT on its pivot and is not RUP. |
| `rat_pigeonhole` | Pigeonhole, 702 additions, 72 RAT, 14,047 propagations. |
| `vdw_a217058_n21` | See below. |

## `vdw_a217058_n21`

A van der Waerden instance from the computation behind **OEIS A217058**, a
sequence whose value `a(12) = 57` is published. The formula is 157 variables and
552 clauses; the refutation is 559 additions, 519 RUP and 40 RAT, with 633
deletions and 20,883 propagations. The proof was produced by `kissat`, not by
hand and not by anything in either repository.

This is the fixture worth having. Everything else here is a test; this is a real
refutation that a published mathematical claim rests on, and the checker whose
rule is proved sound in this repository replays it and agrees.

## The negatives

| Fixture | Why it must be rejected |
| --- | --- |
| `d08_satisfiable_formula` | The formula has a model. No proof of it can be accepted, and `no_false_accept` says so for every proof, not just this one. |
| `d09_trail_leak_between_candidates` | Built to catch a checker that does not unwind its trail between RAT candidates. |
| `d10_duplicate_clause_deleted_once` | A duplicated clause deleted once; the other copy must stay live. |

## Reproducing them

They are byte-identical copies. Refute's `tools/gen_fixtures.sh` regenerates the
generated ones from the solver; the `vdw_a217058_n21` formula is imported and its
proof re-derived by the same `kissat` invocation as the rest.
