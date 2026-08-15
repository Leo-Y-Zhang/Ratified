/-
Steps, derivations, and the theorem behind `s VERIFIED`.

`checkStep` is `Refute`'s per-addition rule, in the order the Rust performs it
(`src/drat/checker.rs::check`): tautology, then RUP, then RAT on the lemma's
first literal. `checkProof` is the run: additions must be justified, deletions
are unconditional, and a justified addition of the empty clause ends the proof.

`checkProof_sound` is what a reader of the checker's output is entitled to
conclude.
-/
import Ratified.RAT

namespace Ratified

/-- A line of a DRAT proof. -/
inductive Step where
  | add (c : Clause)
  | del (c : Clause)
  deriving Repr, DecidableEq

/-- A clause containing a literal and its complement.

`Refute` reaches the same verdict by a different route: it assumes the lemma
false literal by literal and stops if one is already true. The two agree, and
the permissiveness is deliberate — a tautology can be added safely and can never
be the empty clause, so rejecting one would be a false rejection with no safety
benefit. -/
def isTaut (c : Clause) : Bool := c.any (fun l => decide (l.negate ∈ c))

theorem satClause_of_isTaut {a : Assign} {c : Clause} (h : isTaut c = true) :
    satClause a c = true := by
  simp only [isTaut, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨l, hl, hln⟩ := h
  cases hb : satLit a l with
  | true => exact satClause_of_mem hl hb
  | false => exact satClause_of_mem hln (by simp [hb])

/-- RAT on the lemma's first literal, which is the pivot `Refute` uses.

The empty clause has no first literal, so it has no pivot and this returns
`false`. That is load-bearing: a checker that lets the last line through as a
formality accepts every file ending in `0`, which is every file. The empty
clause has to be RUP. -/
def ratOnHead (f : Formula) (c : Clause) : Bool :=
  match c with
  | [] => false
  | p :: _ => isRAT f c p

/-- The addition rule, in `Refute`'s order. -/
def checkStep (f : Formula) (c : Clause) : Bool :=
  isTaut c || isRUP f c || ratOnHead f c

/-- **Step soundness.** A justified addition never turns a satisfiable formula
unsatisfiable. -/
theorem checkStep_sound {f : Formula} {c : Clause} (h : checkStep f c = true) :
    Satisfiable f → Satisfiable (c :: f) := by
  intro hs
  simp only [checkStep, Bool.or_eq_true] at h
  rcases h with (ht | hr) | hrat
  · obtain ⟨a, ha⟩ := hs
    refine ⟨a, satFormula_eq_true_iff.mpr ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxf
    · exact satClause_of_isTaut ht
    · exact satClause_of_satFormula ha hxf
  · exact satisfiable_cons_of_isRUP hr hs
  · cases c with
    | nil => simp [ratOnHead] at hrat
    | cons p rest => exact isRAT_sound (by simp) hrat hs

/-- Deletion cannot make a satisfiable formula unsatisfiable: the result is a
sublist of the input. `Refute` is permissive about deleting a clause it does not
hold, for the same reason — deletion only ever takes tools away from the
checker. -/
theorem satisfiable_erase {f : Formula} {c : Clause} :
    Satisfiable f → Satisfiable (f.erase c) := by
  rintro ⟨a, ha⟩
  refine ⟨a, satFormula_eq_true_iff.mpr ?_⟩
  intro x hx
  exact satClause_of_satFormula ha (List.mem_of_mem_erase hx)

/-- A run of the checker. `true` is `s VERIFIED`.

A proof that ends without deriving the empty clause is not a refutation, which
is why the empty list is `false` rather than `true`. -/
def checkProof (f : Formula) : List Step → Bool
  | [] => false
  | .add c :: rest => checkStep f c && (c.isEmpty || checkProof (c :: f) rest)
  | .del c :: rest => checkProof (f.erase c) rest

/-- **The theorem.** If the checker accepts a proof of `f`, then `f` has no
model.

Everything above is in service of this one statement, and this is the statement
a reader of `s VERIFIED` is entitled to rely on — for the formalised rule. What
it does not cover is set out in the README, and the gap is real: this theorem is
about these definitions, not about the Rust that implements them. -/
theorem checkProof_sound : ∀ (f : Formula) (steps : List Step),
    checkProof f steps = true → Unsatisfiable f := by
  intro f steps
  induction steps generalizing f with
  | nil => intro h; simp [checkProof] at h
  | cons s rest ih =>
      cases s with
      | add c =>
          intro h
          simp only [checkProof, Bool.and_eq_true, Bool.or_eq_true] at h
          obtain ⟨hstep, hrest⟩ := h
          intro hsat
          have hcons : Satisfiable (c :: f) := checkStep_sound hstep hsat
          rcases hrest with hempty | hrec
          · -- The empty clause was derived, and nothing satisfies it.
            have : c = [] := List.isEmpty_iff.mp hempty
            subst this
            exact unsat_of_mem_nil (by simp) hcons
          · exact ih (c :: f) hrec hcons
      | del c =>
          intro h hsat
          simp only [checkProof] at h
          exact ih (f.erase c) h (satisfiable_erase hsat)

/-- **No false accepts.** No input whatsoever makes the checker refute a
satisfiable formula.

`Refute` can only approach this by fixture: `src/drat/checker.rs` names the
satisfiable-formula tests as the controls that matter, and the 10,000-case
differential run against `drat-trim` reports zero false accepts. Those are
statements about the inputs that were tried. This one quantifies over every
proof there is. -/
theorem no_false_accept {f : Formula} (hsat : Satisfiable f) (steps : List Step) :
    checkProof f steps = false := by
  cases hc : checkProof f steps with
  | false => rfl
  | true => exact absurd hsat (checkProof_sound f steps hc)

end Ratified
