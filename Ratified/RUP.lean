/-
Reverse unit propagation.

A clause `C` is RUP with respect to `F` when assuming every literal of `C` false
and propagating reaches a conflict. The theorem below says that this is not just
evidence that `C` may be added — it is evidence that `C` was already implied:
every model of `F` satisfies `C`.
-/
import Ratified.Propagate

namespace Ratified

/-- The trail that assumes a clause false. -/
def negTrail (c : Clause) : List Lit := c.map Lit.negate

/-- How much propagation to allow.

Each propagation step assigns a literal that `isUnitOn` required to be
unassigned, so no variable is assigned twice and the number of literal
occurrences in the instance bounds the number of steps. This is an
over-approximation and deliberately so: fuel can only cause a refusal, never an
acceptance (see the note on `propagate`), so a loose bound costs time and
nothing else. -/
def fuelFor (f : Formula) (c : Clause) : Nat :=
  f.foldl (fun n cl => n + cl.length) 0 + c.length + 1

/-- The RUP check, as `Refute` performs it on the DRAT path: negate the lemma,
propagate, look for a conflict. -/
def isRUP (f : Formula) (c : Clause) : Bool :=
  (propagate f (fuelFor f c) (negTrail c)).isNone

/-- Assuming a clause false is consistent exactly when the clause is false. -/
theorem agree_negTrail {a : Assign} {c : Clause} (hc : satClause a c = false) :
    agree a (negTrail c) := by
  intro l hl
  simp only [negTrail, List.mem_map] at hl
  obtain ⟨x, hx, rfl⟩ := hl
  have hxf : satLit a x = false := satClause_eq_false_iff.mp hc x hx
  simp [hxf]

/-- **RUP soundness.** A RUP clause is entailed: every model of `f` satisfies
it. Adding it therefore changes nothing about which assignments satisfy the
formula, which is more than satisfiability preservation. -/
theorem isRUP_sound {f : Formula} {c : Clause} (h : isRUP f c = true)
    {a : Assign} (hf : satFormula a f = true) : satClause a c = true := by
  cases hc : satClause a c with
  | true => rfl
  | false =>
      exfalso
      have hne := propagate_ne_none hf (fuelFor f c) (negTrail c) (agree_negTrail hc)
      simp only [isRUP, Option.isNone_iff_eq_none] at h
      exact hne h

/-- The form the derivation theorem consumes. -/
theorem satisfiable_cons_of_isRUP {f : Formula} {c : Clause} (h : isRUP f c = true) :
    Satisfiable f → Satisfiable (c :: f) := by
  rintro ⟨a, ha⟩
  refine ⟨a, satFormula_eq_true_iff.mpr ?_⟩
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hxf
  · exact isRUP_sound h ha
  · exact satClause_of_satFormula ha hxf

end Ratified
