# Ratified

A machine-checked soundness proof, in Lean 4, of the two proof rules that SAT
solvers use to certify that a formula has no solution: **RUP** (reverse unit
propagation) and **RAT** (resolution asymmetric tautology).

The rules are the ones a DRAT checker implements. I wrote such a checker in Rust
first — [Refute](https://github.com/Leo-Y-Zhang/Refute) — and its design document
justifies the RAT rule in a paragraph that ends "that is the whole argument".
This repository is that argument, checked by a machine instead of by a reader.

It is not only a proof. `checkProof` is an executable function, so the same
definition the theorem is about ships as a command-line checker — and it replays
real certificates, including the refutation behind a published van der Waerden
number.

No `mathlib`, no dependencies at all: Lean core only. `lake build` takes a few
seconds from a warm toolchain.

## The theorem

```lean
theorem checkProof_sound : ∀ (f : Formula) (steps : List Step),
    checkProof f steps = true → Unsatisfiable f
```

`checkProof` is an executable function. Given a formula and a list of DRAT steps
it returns a `Bool`, and the theorem says that when it returns `true` the formula
has no satisfying assignment. That is exactly the claim a checker makes when it
prints `s VERIFIED`.

The corollary is the one a checker's test suite spends most of its effort
approximating:

```lean
theorem no_false_accept {f : Formula} (hsat : Satisfiable f) (steps : List Step) :
    checkProof f steps = false
```

No input whatsoever makes the checker refute a satisfiable formula. Refute can
only approach that by fixture — it names its satisfiable-formula tests as the
controls that matter, and a 10,000-case differential run against `drat-trim`
found zero false accepts. Those are statements about the inputs that were tried.
This one quantifies over every proof there is.

## What is proved

- **Propagation soundness.** If unit propagation reaches a conflict from a trail,
  no model of the formula agrees with that trail. Every later result is an
  application of this.
- **Propagation progress.** A forced literal is always on a variable the trail
  has no opinion about, so propagation assigns each variable at most once and the
  trail it returns never mentions one twice. That is what makes a finite fuel
  bound exist at all — it was a comment on `fuelFor` before it was a theorem.
- **RUP soundness.** A RUP clause is *entailed*: every model of the formula
  already satisfies it.
- **RAT soundness.** A RAT clause on a pivot it contains can be added without
  turning a satisfiable formula unsatisfiable. The proof is constructive — it
  takes a model and flips one variable.
- **Tautologies and deletions.** Adding a tautology is safe; deleting a clause is
  safe.
- **The derivation.** Composing the above over a list of steps: an accepted proof
  means the formula is unsatisfiable.

RAT is genuinely weaker than RUP, and the difference is visible in a worked
example the kernel decides: `Ratified/Examples.lean` exhibits a clause that the
RAT check accepts together with a model of the formula that falsifies it. So a
RAT step really can add a clause that was not implied, which is why its theorem
concludes that satisfiability is preserved rather than that the clause follows.

## Running it

```
lake build ratified
.lake/build/bin/ratified fixtures/vdw_a217058_n21.cnf fixtures/vdw_a217058_n21.drat
s VERIFIED
```

That pair is a van der Waerden instance from the computation behind **OEIS
A217058**, whose value `a(12) = 57` is published: 157 variables, 552 clauses, and
a 559-step refutation with 519 RUP steps, 40 genuine RAT steps and 633 deletions,
produced by `kissat`. The function whose soundness is proved above replays it and
accepts it, in about seven seconds.

`fixtures/` holds nine pairs and `fixtures/EXPECTED` the verdict each must
receive — six accepted, three rejected — together with a tenth row whose pair
deliberately does not exist. `tools/fixtures.sh` checks all ten and runs in CI.
The three rejections are the ones that carry the weight: a checker that accepts
everything passes the six positives. The tenth pins the third answer: an input
the checker could not read exits 2, not 1, because "I never saw a proof" is not
the same claim as "this proof is bad".

## What is not proved

This matters more than the list above, so it is specific.

The theorem is about the definitions in this repository. It is **not** a
verification of Refute, and Refute's Rust is **not** extracted from it. The two
were written to the same rule, by the same person, and agree on the worked
examples — that is all the connection there is.

Concretely, out of scope here:

- **The readers.** `Ratified/Parse.lean` turns DIMACS and DRAT text into Lean
  values and is completely unverified. It is the boundary: the theorem starts
  where the reader returns. It fails loudly rather than skipping what it cannot
  understand, because a reader that silently dropped a malformed clause would
  make a verdict meaningless while still printing it — but that is a design
  choice, not a proof.
- **The compiler.** The binary is produced by Lean's compiler, not reduced by its
  kernel, so running it trusts the compiler in the way any extracted verified
  program does. The kernel-checked version of the same claim, for formulas small
  enough to decide that way, is in `Ratified/Examples.lean`; `F₁_unsat` is a
  theorem obtained by handing the checker's verdict to `checkProof_sound`, with
  no compiler involved.
- **The data structures.** This model uses lists and linear scans. A real checker
  uses a clause arena, watched literals, an occurrence index and a deletion
  index, and a bug in any of those is a bug this proof cannot see. In particular
  the completeness of the RAT candidate set is trivial here — it is a `filter`
  over the formula — and is exactly the delicate part in an implementation. The
  price is measured in `docs/DIFFERENTIAL.md`: about 130× slower than Refute on
  the largest fixture.
- **Resource limits.** Absent. A hostile input can make the checker slow.
- **Completeness.** Nothing here says the checker accepts every valid proof. The
  fuel bound on propagation makes that explicit: running out of fuel refuses to
  claim a conflict, which can only cause a rejection, so soundness does not
  depend on the bound being generous. What *is* proved is that a finite bound
  exists — `propagate_nodup` — because no variable is ever assigned twice. What
  is not proved is that the particular value `fuelFor` computes is always large
  enough. Closing that needs a pigeonhole count of the trail against the
  instance's variables, and Lean's core library does not carry the list lemmas
  for it; today the question is answered by executable examples instead.

## Evidence

**Axioms.** Pinned in `Ratified/Audit.lean` with `#guard_msgs`, so the build
fails if the list ever changes:

```
'Ratified.checkProof_sound' depends on axioms: [propext, Quot.sound]
```

No `sorryAx`, so nothing is left unproved. No `Lean.ofReduceBool`, so no
`native_decide` moved a computation out of the kernel and into the compiler.
Not even `Classical.choice`.

**Mutation evidence.** A proof that has never been observed failing is
decoration. `MUTATIONS.md` records seven rules that could be quietly dropped, the
mutation that drops each one, and the build failure that resulted — **seven of
seven killed**. The split is the interesting part: the six soundness rules are
caught by proofs failing to compile, and the one completeness rule (the fuel
bound) is invisible to every proof and caught only by an executable check. That
is what the design predicted, and it is why both gates exist.

CI re-runs the whole campaign on hardware that is not mine and fails if the
regenerated `MUTATIONS.md` differs from the committed one, so the evidence is
checked rather than asserted.

**Worked examples.** 15 `#guard` checks, decided by the kernel at build time: a
refutation the checker accepts, a satisfiable formula it must not, the RAT
example above, and the individual rules that are load-bearing on their own — the
empty clause having no pivot, and a repeated literal not being a tautology.

**Agreement with an independent implementation.** Refute is a DRAT checker in
Rust, written to the same rule and sharing no code with this. On all nine
fixtures the two agree — **9 agreed, 0 disagreed** — including the vdW
refutation, the pigeonhole proof, and the satisfiable formula both must reject.
Verdicts are compared by exit code so wording cannot mask a difference.
`docs/DIFFERENTIAL.md` has the table, the timings, and what the result is and is
not evidence of.

## Building

```
lake build
```

The toolchain is pinned in `lean-toolchain`. With
[elan](https://github.com/leanprover/elan) installed, `lake` fetches it on first
build; no system-wide install and no administrator rights are needed.

To re-derive the mutation evidence, replay the corpus, or compare against Refute:

```
python tools/mutations.py
sh tools/fixtures.sh .lake/build/bin/ratified fixtures
sh tools/differential.sh <ratified-binary> <refute-binary> <fixture-dir>
```

## Layout

| Module | What is in it |
| --- | --- |
| `Ratified/Basic.lean` | Literals, clauses, formulas, assignments, satisfaction |
| `Ratified/Propagate.lean` | The trail, unit propagation, and its soundness theorem |
| `Ratified/RUP.lean` | The RUP check and its soundness theorem |
| `Ratified/RAT.lean` | The RAT check and the witness-flip soundness theorem |
| `Ratified/Proof.lean` | Steps, the derivation, `checkProof_sound`, `no_false_accept` |
| `Ratified/Examples.lean` | Worked examples, decided by the kernel |
| `Ratified/Audit.lean` | The pinned axiom list |
| `Ratified/Parse.lean` | DIMACS and DRAT readers — **unverified**, the boundary |
| `Main.lean` | The command line |

899 lines of Lean for the proof, 166 more for the reader and the command line.
40 theorems, no dependencies.

## Licence

MIT. See `LICENSE`.
