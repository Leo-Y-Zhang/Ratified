/-
Resolution asymmetric tautology, and the theorem that justifies the rule.

`Refute`'s design document states the rule and its justification in one
paragraph (`docs/TDD.md`, "Why it is sound"):

> A clause `C` is RAT on a pivot `p` in `C` with respect to formula `F` when,
> for every clause `D` in `F` with `-p` in `D`, the resolvent `C or (D \ {-p})`
> is implied by `F` by unit propagation. Adding a RAT clause preserves
> satisfiability, so if `F + C` is unsatisfiable then `F` is. That is the whole
> argument, applied once per addition and composed backwards from the empty
> clause.

`isRAT_sound` is that sentence, checked. Unlike RUP, a RAT clause need not be
entailed — the conclusion really is only that satisfiability is preserved, and
the proof is constructive: it takes a model of `F` and builds a model of
`F + C` by flipping one variable.
-/
import Ratified.RUP

namespace Ratified

/-- `C ∨ (D \ {¬p})`, the resolvent of the lemma and a candidate on the pivot. -/
def resolvent (c d : Clause) (p : Lit) : Clause :=
  c ++ d.filter (fun l => decide (l ≠ p.negate))

/-- Every clause of `f` holding `¬p`.

Completeness of this list is the first of the three ways `Refute`'s source says
a checker can lose the argument: miss one clause and the RAT condition was never
checked. Here it is a `filter` over the whole formula, so there is nothing to
miss. -/
def ratCandidates (f : Formula) (p : Lit) : Formula :=
  f.filter (fun d => decide (p.negate ∈ d))

/-- The RAT check on a given pivot. A lemma with no candidates passes
vacuously, by the same `all` that checks the others — the second of the three,
and the reason there is no separate vacuous path to drift. -/
def isRAT (f : Formula) (c : Clause) (p : Lit) : Bool :=
  (ratCandidates f p).all (fun d => isRUP f (resolvent c d p))

/-! ### Flipping one variable -/

/-- `a` with variable `v` reassigned to `b`. -/
def flipAt (a : Assign) (v : Nat) (b : Bool) : Assign := fun w => if w = v then b else a w

@[simp] theorem satLit_flipAt_of_ne {a : Assign} {v : Nat} {b : Bool} {l : Lit}
    (h : l.var ≠ v) : satLit (flipAt a v b) l = satLit a l := by
  simp [satLit, flipAt, h]

@[simp] theorem satLit_flipAt_self (a : Assign) (p : Lit) :
    satLit (flipAt a p.var p.pol) p = true := by
  simp [satLit, flipAt]

/-- A literal true under `a`, distinct from `¬p`, where `p` is false under `a`,
cannot be on `p`'s variable — so flipping `p` leaves it alone. -/
theorem var_ne_of_true {a : Assign} {p l : Lit} (hp : satLit a p = false)
    (hl : satLit a l = true) (hne : l ≠ p.negate) : l.var ≠ p.var := by
  intro hv
  rcases Lit.eq_or_eq_negate hv with rfl | h
  · rw [hp] at hl; exact Bool.noConfusion hl
  · exact hne h

/-- **RAT soundness.** If `c` passes the RAT check on a pivot it contains, then
`c` may be added without turning a satisfiable formula unsatisfiable.

The witness is explicit: take a model of `f`; if it already satisfies `c` it is
the model, and otherwise flipping the pivot's variable to make `c` true keeps
every clause of `f` true. -/
theorem isRAT_sound {f : Formula} {c : Clause} {p : Lit}
    (hp : p ∈ c) (h : isRAT f c p = true) :
    Satisfiable f → Satisfiable (c :: f) := by
  rintro ⟨a, ha⟩
  cases hc : satClause a c with
  | true =>
      refine ⟨a, satFormula_eq_true_iff.mpr ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxf
      · exact hc
      · exact satClause_of_satFormula ha hxf
  | false =>
      -- The pivot is false under `a`, because every literal of `c` is.
      have hpf : satLit a p = false := satClause_eq_false_iff.mp hc p hp
      refine ⟨flipAt a p.var p.pol, satFormula_eq_true_iff.mpr ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxf
      · -- The lemma itself: the pivot now holds.
        exact satClause_of_mem hp (satLit_flipAt_self a p)
      · by_cases hcand : p.negate ∈ x
        · -- A candidate: its resolvent is RUP, and the witness cannot be in `c`.
          have hmem : x ∈ ratCandidates f p := by
            simp only [ratCandidates, List.mem_filter, decide_eq_true_eq]
            exact ⟨hxf, hcand⟩
          have hrup : isRUP f (resolvent c x p) = true := by
            simp only [isRAT, List.all_eq_true] at h
            exact h x hmem
          have hres : satClause a (resolvent c x p) = true := isRUP_sound hrup ha
          obtain ⟨l, hlmem, hlt⟩ := satClause_eq_true_iff.mp hres
          simp only [resolvent, List.mem_append, List.mem_filter, decide_eq_true_eq] at hlmem
          rcases hlmem with hlc | ⟨hlx, hlne⟩
          · -- Impossible: no literal of `c` is true under `a`.
            rw [satClause_eq_false_iff.mp hc l hlc] at hlt
            exact Bool.noConfusion hlt
          · exact satClause_of_mem hlx
              (by rw [satLit_flipAt_of_ne (var_ne_of_true hpf hlt hlne)]; exact hlt)
        · -- Not a candidate: `x` cannot be satisfied by `¬p`, so its witness survives.
          obtain ⟨l, hlmem, hlt⟩ :=
            satClause_eq_true_iff.mp (satClause_of_satFormula ha hxf)
          have hlne : l ≠ p.negate := by
            intro hEq; exact hcand (hEq ▸ hlmem)
          exact satClause_of_mem hlmem
            (by rw [satLit_flipAt_of_ne (var_ne_of_true hpf hlt hlne)]; exact hlt)

end Ratified
