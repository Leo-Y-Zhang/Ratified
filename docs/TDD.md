# TDD — Ratified

## Shape of the development

Six modules, each depending only on the ones above it.

```
Basic       literals, clauses, formulas, assignments, satisfaction
  └ Propagate   the trail, agreement, unit propagation, propagation soundness
      └ RUP         the RUP check, RUP soundness
          └ RAT         the RAT check, the witness flip, RAT soundness
              └ Proof       steps, checkProof, checkProof_sound, no_false_accept
                  ├ Examples    worked examples decided by the kernel
                  │   └ Audit       the pinned axiom list
                  └ Parse       DIMACS and DRAT readers -- UNVERIFIED
                      └ Main        the command line
```

The dependency order is also the argument's order. Nothing later is used earlier,
and there are no mutual dependencies.

`Parse` and `Main` sit deliberately at the bottom and outside the argument.
Everything above `Parse` is a statement about Lean values; `Parse` is what turns
bytes into them, and it is where the guarantee stops. Keeping it in a separate
module with that written in its header is the cheapest way to stop the boundary
from blurring — the temptation, once a binary prints `s VERIFIED` on a real
certificate, is to describe the whole pipeline as verified.

## Modelling decisions, and why

**Total assignments for semantics, a trail for partial information.**
`Assign := Nat → Bool` is total, because satisfiability quantifies over total
assignments and making the semantics partial would complicate every statement to
buy nothing. Partial information lives in the trail, a `List Lit` of literals
assumed true, and `agree` is the only bridge between the two. A trail that holds
both a literal and its complement is agreed with by nothing, which is the correct
reading: such a state is already a conflict.

**Bool-valued satisfaction.** `satClause` and `satFormula` return `Bool` rather
than `Prop`. That makes the worked examples decidable by the kernel — a claim
like "this assignment satisfies this formula but falsifies this clause" is then
`#guard`-checkable rather than a proof obligation — and costs nothing in the
theorems, which say `= true` or `= false` throughout.

**Fuel-bounded propagation.** `propagate` takes a `Nat` of fuel and returns
`some trail` when it runs out. This is the decision that keeps the file small:
propagation to a genuine fixpoint would need a termination argument (each step
assigns a previously unassigned variable, so the number of variables bounds it),
and that argument earns nothing, because running out of fuel *refuses to claim a
conflict*. A fuel bound can only cause a rejection, never an acceptance, so
soundness is independent of it. `propagate_ne_none` is stated for all `n`, which
is where that independence is visible.

The cost is that completeness now depends on `fuelFor` being generous, and no
theorem can see that. The mutation campaign makes the consequence concrete:
setting the fuel to zero leaves every soundness proof compiling and breaks the
executable examples. That is the intended division of labour between the two
gates, demonstrated rather than asserted.

What *is* proved about the bound is that a finite one exists. `findUnit_var_fresh`
says a forced literal is always on a variable the trail has no opinion about —
`isUnitOn` demands the literal be unassigned, and the only two literals on a
variable are a literal and its complement — and `propagate_nodup` lifts that
through the recursion: the returned trail never mentions a variable twice. So the
instance's variable count bounds the number of steps.

Going from there to "`fuelFor` is always large enough" is a pigeonhole count of
the trail against the instance's variables. Lean's core library does not carry
the list lemmas that argument needs, and importing `mathlib` for them would cost
the whole no-dependency property, which is worth more here than closing a gap
that costs a rejection rather than a false accept.

**Hand-written searches.** `findConflict`, `findUnitLit` and `findUnit` are
written by explicit recursion rather than through `List.findSome?`, so each
specification lemma is a two-case induction that depends on nothing. The library
route would have been shorter to write and longer to trust.

## The rule, as implemented here

`checkStep` follows Refute's `src/drat/checker.rs::check` in order:

1. **Tautology.** `c` holds a literal and its complement. Accepted: adding it
   preserves satisfiability and it can never be the empty clause, so rejecting
   would be a false rejection with no safety benefit.
2. **RUP.** Assume every literal of `c` false, propagate, look for a conflict.
3. **RAT on the first literal.** For every clause of the formula holding the
   negated pivot, the resolvent `C ∨ (D \ {¬p})` must be RUP.

Three details are load-bearing and each has a recorded mutation.

- **The pivot is the lemma's first literal as written.** The empty clause has no
  first literal, so `ratOnHead` returns `false` on it and the empty clause has to
  be RUP. A checker that treats the last line as a formality accepts every file
  that ends in `0`.
- **The candidate set is every clause holding `¬p`.** Here that is a `filter`, so
  completeness is trivial; in an implementation backed by an occurrence index it
  is the delicate part, and missing one clause means the condition was never
  checked.
- **The resolvent is `C ∨ (D \ {¬p})`, lemma included.** Dropping the lemma is
  checking a different clause.

A self-contradictory trail counts as a conflict. This is needed because a
resolvent can be a tautology; Refute reaches the same conclusion through
`check_resolvent`, which returns "refuted" the moment a literal it is about to
assume false is already true.

## The RAT proof

The only proof in the development with any content.

Let `a` satisfy `f`, and let `c` pass the RAT check on a pivot `p ∈ c`. If `a`
satisfies `c` there is nothing to do. Otherwise every literal of `c` is false
under `a`, in particular `p`, and the witness is `a` with `p`'s variable flipped
to `p`'s polarity. That satisfies `c`. For a clause `d` of `f`:

- If `¬p ∉ d`, then `a` satisfies `d` via some literal `l`. `l` cannot be `p`,
  because `p` is false under `a`, and `l` cannot be `¬p`, which is not in `d`. So
  `l` is on a different variable and the flip leaves it true.
- If `¬p ∈ d`, then `d` is a candidate, so `C ∨ (D \ {¬p})` is RUP and therefore
  entailed, so `a` satisfies it. The satisfied literal is not in `c` — nothing in
  `c` is true under `a` — so it is in `d`, is not `¬p`, and is not `p`. Same
  conclusion.

The two cases share their last step, which is the lemma `var_ne_of_true`.

## Gates

| Gate | What it catches | Where |
| --- | --- | --- |
| Kernel type-checking | Any unsound step in any proof | `lake build` |
| `#guard` | The executable checker returning the wrong verdict | `Examples.lean` |
| `#guard_msgs` on `#print axioms` | A `sorry` or a `native_decide` appearing anywhere | `Audit.lean` |
| Mutation campaign | A rule that is stated but not actually load-bearing | `tools/mutations.py` |
| Fixture corpus | The compiled checker giving the wrong verdict on a real proof | `tools/fixtures.sh` |
| Differential run | The rule as proved and the rule as implemented in Rust diverging | `tools/differential.sh` |
| gitleaks, pinned binary, full history | Secrets | CI |

The mutation campaign runs in CI and the regenerated `MUTATIONS.md` must match
the committed one, so the evidence is re-derived on hardware that is not the
author's rather than taken on trust.

The secret scan uses the pinned `gitleaks` binary over `--log-opts=--all` rather
than the published action, which scans only the pushed range: a secret committed
once and never touched again is invisible to the action, and on a repository's
first push it fails outright because the root commit has no parent.
