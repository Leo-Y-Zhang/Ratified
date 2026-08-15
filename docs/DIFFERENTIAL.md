# Agreement with an independent implementation

The theorems in this repository are about `checkProof`. They say nothing about
any other program, and in particular nothing about
[Refute](https://github.com/Leo-Y-Zhang/Refute), the DRAT checker in Rust that
prompted this work. The two share a rule and nothing else — no code, no
extraction, no generated interface.

That makes them worth running against each other. Where they agree, two
implementations written from the same rule reached the same verdict; where they
disagreed, at least one would be wrong about the rule, and finding out which
would be the interesting part.

## Result

Every formula/proof pair in `fixtures/`, both checkers, verdict compared by exit
code so wording cannot mask a difference:

| Fixture | Ratified | Refute | |
| --- | --- | --- | --- |
| `tiny_unsat` | VERIFIED | VERIFIED | agree |
| `empty_clause_in_cnf` | VERIFIED | VERIFIED | agree |
| `deletes_originals` | VERIFIED | VERIFIED | agree |
| `real_rat_proof` | VERIFIED | VERIFIED | agree |
| `rat_pigeonhole` | VERIFIED | VERIFIED | agree |
| `vdw_a217058_n21` | VERIFIED | VERIFIED | agree |
| `d08_satisfiable_formula` | NOT VERIFIED | NOT VERIFIED | agree |
| `d09_trail_leak_between_candidates` | NOT VERIFIED | NOT VERIFIED | agree |
| `d10_duplicate_clause_deleted_once` | NOT VERIFIED | NOT VERIFIED | agree |

**9 agreed, 0 disagreed.**

Reproduce with:

```
tools/differential.sh <ratified-binary> <refute-binary> <fixture-dir>
```

## Cost

Measured on the same machine, wall clock including process start, one run each.
Refute is a real checker — clause arena, watched literals, occurrence index.
This one is lists and linear scans, because it was written to be read and to be
proved about.

| Fixture | Formula | Proof | Ratified | Refute |
| --- | ---: | ---: | ---: | ---: |
| `tiny_unsat` | 86 B | 34 B | 66 ms | 67 ms |
| `real_rat_proof` | 437 B | 1.9 KB | 76 ms | 55 ms |
| `rat_pigeonhole` | 1.3 KB | 20.4 KB | 5,848 ms | 55 ms |
| `vdw_a217058_n21` | 7.1 KB | 19.9 KB | 7,257 ms | 57 ms |

About 130× slower on the largest pair. That is the honest price of a model whose
data structures were chosen to make the proofs short, and it is not a defect to
be apologised for — but it does bound what this binary is for. It replays real
certificates of this size in seconds. It would not replay a megabyte one.

## What this is and is not evidence of

**Is:** that the rule as stated in `Ratified/Proof.lean` and the rule as
implemented in Refute's Rust agree on nine proofs, six of which a solver
produced, including a 559-step refutation with 40 genuine RAT steps.

**Is not:** a verification of Refute. Agreement on nine inputs is agreement on
nine inputs. Refute's own differential harness — 10,000 generated cases against
`drat-trim` — is the broader version of this argument, and it too is a statement
about inputs that were tried.

The one claim here that quantifies over everything rather than over a corpus is
`no_false_accept`, and it is about this repository's checker alone.
