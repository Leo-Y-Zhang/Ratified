/-
Worked examples, all decided by the kernel.

Every claim in this file is a `#guard` or a theorem, so `lake build` fails if any
of them stops holding. Two of them are the ones worth arguing about: that a RAT
clause need not be entailed, and that no proof at all refutes a satisfiable
formula.
-/
import Ratified.Proof

namespace Ratified

/-- The variable, asserted. -/
def pos (v : Nat) : Lit := ⟨v, true⟩

/-- The variable, negated. -/
def neg (v : Nat) : Lit := ⟨v, false⟩

/-! ### A refutation the checker accepts

The four clauses over two variables that rule out every assignment. The proof
adds the unit `(1)`, deletes a clause to exercise that path, and then derives the
empty clause. -/

def F₁ : Formula :=
  [[pos 1, pos 2], [pos 1, neg 2], [neg 1, pos 2], [neg 1, neg 2]]

def proof₁ : List Step :=
  [.add [pos 1], .del [pos 1, pos 2], .add []]

#guard checkProof F₁ proof₁ = true

/-- The checker's verdict, cashed in for the mathematical statement. This is the
whole point of the development: `s VERIFIED` on the left, `Unsatisfiable` on the
right, and `checkProof_sound` in between. -/
theorem F₁_unsat : Unsatisfiable F₁ := checkProof_sound F₁ proof₁ (by decide)

/-! A justified addition that never reaches the empty clause is not a
refutation. -/

#guard checkProof F₁ [.add [pos 1]] = false

/-! ### RAT is genuinely weaker than entailment

`(1 ∨ ¬2)` is blocked on the pivot `1` with respect to `{(¬1 ∨ 2)}`: the only
candidate resolves to a tautology. So the checker accepts it — and yet the
formula does not entail it, as the witness below shows.

This is why `isRAT_sound` concludes that satisfiability is preserved and not, as
`isRUP_sound` does, that the clause was already implied. The two rules have
genuinely different strengths and the difference is visible in one example. -/

def F₃ : Formula := [[neg 1, pos 2]]
def C₃ : Clause := [pos 1, neg 2]

#guard isRUP F₃ C₃ = false
#guard isRAT F₃ C₃ (pos 1) = true
#guard checkStep F₃ C₃ = true

/-- Sets variable 1 false and everything else true. -/
def witness₃ : Assign := fun v => if v = 1 then false else true

#guard satFormula witness₃ F₃ = true
#guard satClause witness₃ C₃ = false

/-- `F₃` has a model that falsifies `C₃`, so `C₃` is not entailed — and the
checker accepted it anyway, soundly. -/
theorem C₃_not_entailed : ∃ a : Assign, satFormula a F₃ = true ∧ satClause a C₃ = false :=
  ⟨witness₃, by decide, by decide⟩

/-! ### The controls

A formula the checker must never refute, and the proof that it never does. -/

def F₂ : Formula := [[pos 1, pos 2], [neg 1, pos 2]]

/-- Everything true. -/
def modelF₂ : Assign := fun _ => true

theorem F₂_sat : Satisfiable F₂ := ⟨modelF₂, by decide⟩

/-- Not a fixture: a theorem, over every proof there is. -/
theorem F₂_never_refuted (steps : List Step) : checkProof F₂ steps = false :=
  no_false_accept F₂_sat steps

/-! The two shapes a checker is most likely to wave through, checked
individually anyway. -/

#guard checkProof F₂ [.add []] = false
#guard checkProof F₂ [.add [neg 2], .add []] = false

/-! ### The rules that are load-bearing on their own -/

/-! The empty clause has no first literal, so it has no pivot and RAT cannot be
attempted on it. A checker that treats the last line as a formality accepts
every file that ends in `0`. -/

#guard ratOnHead F₃ [] = false
#guard checkStep F₃ [] = false

/-! A repeated literal is not a tautology. `-2 -2` is the clause `-2`; reading
the repeat as `x ∨ ¬x` would accept a lemma before anything was checked. -/

#guard isTaut [neg 2, neg 2] = false
#guard isTaut [pos 2, neg 2] = true

/-- A pivot with no candidates passes vacuously, through the same `all` that
checks the others. -/
def F₄ : Formula := [[pos 2, pos 3]]

#guard ratCandidates F₄ (pos 1) = []
#guard isRAT F₄ [pos 1, pos 5] (pos 1) = true

end Ratified
