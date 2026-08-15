/-
Propositional CNF: syntax, semantics, and the two facts about complementation
that every later proof leans on.

Nothing here is clever. It is written out in full because every theorem in this
development is a statement *about these definitions*, so a reader who disagrees
with the semantics disagrees with the whole thing, and should be able to see
them without reading any proofs.
-/

namespace Ratified

/-- A propositional literal: a variable index and the polarity it is asserted
with. `⟨3, true⟩` is `x₃` and `⟨3, false⟩` is `¬x₃`. -/
structure Lit where
  var : Nat
  pol : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The complement of a literal. -/
def Lit.negate (l : Lit) : Lit := ⟨l.var, !l.pol⟩

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit

/-- A formula is a conjunction of clauses. -/
abbrev Formula := List Clause

/-- A total assignment of truth values to variables.

Totality is a modelling choice and it is the right one here: the rules being
verified are about satisfiability, which quantifies over total assignments.
Partial information lives in the trail (`Ratified.Propagate`), never here. -/
abbrev Assign := Nat → Bool

/-- A literal is satisfied when the assignment agrees with its polarity. -/
def satLit (a : Assign) (l : Lit) : Bool := a l.var == l.pol

/-- A clause is satisfied when at least one of its literals is. The empty
clause is therefore satisfied by nothing, which is what makes deriving it a
refutation. -/
def satClause (a : Assign) (c : Clause) : Bool := c.any (satLit a)

/-- A formula is satisfied when all of its clauses are. -/
def satFormula (a : Assign) (f : Formula) : Bool := f.all (satClause a)

/-- There is an assignment satisfying every clause. -/
def Satisfiable (f : Formula) : Prop := ∃ a : Assign, satFormula a f = true

/-- There is no such assignment. This is what `Refute` prints `s VERIFIED` to
claim, and the conclusion of `checkProof_sound`. -/
def Unsatisfiable (f : Formula) : Prop := ¬ Satisfiable f

/-! ### Complementation -/

@[simp] theorem Lit.negate_var (l : Lit) : l.negate.var = l.var := rfl

@[simp] theorem Lit.negate_negate (l : Lit) : l.negate.negate = l := by
  cases l with
  | mk v p => cases p <;> rfl

/-- The fact the whole development turns on: a literal and its complement
disagree under every assignment. -/
@[simp] theorem satLit_negate (a : Assign) (l : Lit) :
    satLit a l.negate = !satLit a l := by
  cases l with
  | mk v p => cases p <;> cases h : a v <;> simp [satLit, Lit.negate, h]

theorem satLit_eq_false_of_negate (a : Assign) (l : Lit)
    (h : satLit a l.negate = true) : satLit a l = false := by
  have := satLit_negate a l
  rw [h] at this
  cases hl : satLit a l <;> simp [hl] at this ⊢

/-- Two literals on the same variable are equal or complementary. -/
theorem Lit.eq_or_eq_negate {l p : Lit} (h : l.var = p.var) :
    l = p ∨ l = p.negate := by
  cases l with
  | mk lv lp =>
    cases p with
    | mk pv pp =>
      simp only at h
      subst h
      cases lp <;> cases pp <;> simp [Lit.negate]

/-! ### Satisfaction, unfolded

`List.any` and `List.all` are the computational form; these are the shapes the
proofs actually use. They are stated here once so that no later file has to
know how `List.any` is defined. -/

theorem satClause_eq_true_iff {a : Assign} {c : Clause} :
    satClause a c = true ↔ ∃ l ∈ c, satLit a l = true := by
  simp [satClause]

theorem satClause_eq_false_iff {a : Assign} {c : Clause} :
    satClause a c = false ↔ ∀ l ∈ c, satLit a l = false := by
  simp [satClause]

theorem satFormula_eq_true_iff {a : Assign} {f : Formula} :
    satFormula a f = true ↔ ∀ c ∈ f, satClause a c = true := by
  simp [satFormula]

theorem satClause_of_mem {a : Assign} {c : Clause} {l : Lit}
    (hl : l ∈ c) (h : satLit a l = true) : satClause a c = true :=
  satClause_eq_true_iff.mpr ⟨l, hl, h⟩

theorem satClause_of_satFormula {a : Assign} {f : Formula} {c : Clause}
    (h : satFormula a f = true) (hc : c ∈ f) : satClause a c = true :=
  satFormula_eq_true_iff.mp h c hc

/-- The empty clause is satisfied by nothing. -/
@[simp] theorem satClause_nil (a : Assign) : satClause a ([] : Clause) = false := rfl

/-- A formula containing the empty clause is unsatisfiable. This is the base of
the refutation argument and it is this small. -/
theorem unsat_of_mem_nil {f : Formula} (h : ([] : Clause) ∈ f) : Unsatisfiable f := by
  rintro ⟨a, ha⟩
  have := satClause_of_satFormula ha h
  simp at this

end Ratified
