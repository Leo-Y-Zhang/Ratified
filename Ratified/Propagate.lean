/-
Unit propagation, and the one theorem about it that matters: if propagation
reaches a conflict from a trail, no model of the formula agrees with that trail.

This is the part of a DRAT checker with no external witness to police it. In an
LRAT proof the producer names every propagation and the checker only has to
agree; on the DRAT path the engine derives them itself, so a bug that assigns a
literal no clause forces makes every subsequent check easier to pass. `Refute`'s
own source says as much (`src/drat/checker.rs`: "the first thing in this project
that could accept a bad proof with nothing in the file to contradict it"). That
sentence is the reason this file exists.
-/
import Ratified.Basic

namespace Ratified

/-! ### The trail

A trail is the list of literals currently assumed true. It is the partial
assignment, and `agree` is the only bridge between it and a real assignment. -/

/-- Every literal on the trail is true under `a`. A trail that asserts both a
literal and its complement is agreed with by nothing, which is exactly right:
such a state is already a conflict. -/
def agree (a : Assign) (t : List Lit) : Prop := ∀ l ∈ t, satLit a l = true

theorem agree_nil (a : Assign) : agree a ([] : List Lit) := by
  intro l hl; cases hl

theorem agree_cons {a : Assign} {t : List Lit} {l : Lit}
    (hl : satLit a l = true) (ht : agree a t) : agree a (l :: t) := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · subst h; exact hl
  · exact ht x h

/-- The trail assigns `l` false, i.e. it holds `l`'s complement. -/
def isFalse (t : List Lit) (l : Lit) : Bool := decide (l.negate ∈ t)

/-- The trail says nothing about `l`'s variable. -/
def isUnassigned (t : List Lit) (l : Lit) : Bool :=
  !decide (l ∈ t) && !decide (l.negate ∈ t)

/-- A trail literal read through an agreeing assignment. -/
theorem satLit_eq_false_of_isFalse {a : Assign} {t : List Lit} {l : Lit}
    (hag : agree a t) (h : isFalse t l = true) : satLit a l = false := by
  simp only [isFalse, decide_eq_true_eq] at h
  exact satLit_eq_false_of_negate a l (hag _ h)

/-! ### Clause states -/

/-- Every literal of `c` is false under `t`: the clause is refuted. -/
def clauseFalsified (t : List Lit) (c : Clause) : Bool := c.all (isFalse t)

/-- `l` is the one literal of `c` that is not already false, and it is
unassigned: propagating it is forced. -/
def isUnitOn (t : List Lit) (c : Clause) (l : Lit) : Bool :=
  decide (l ∈ c) && isUnassigned t l &&
    c.all (fun l' => decide (l' = l) || isFalse t l')

/-- The trail contradicts itself: it holds some literal and that literal's
complement.

`Refute` reaches this case through `check_resolvent`, which returns "refuted" the
moment a literal it is about to assume false is already true. It matters for
resolvents specifically: `C ∨ (D \ {¬p})` can be a tautology, and a checker that
only ever looks for a falsified *clause* would fail to see the conflict and
reject a sound step. -/
def trailFalsified (t : List Lit) : Bool := t.any (isFalse t)

theorem not_agree_of_trailFalsified {a : Assign} {t : List Lit}
    (hag : agree a t) (h : trailFalsified t = true) : False := by
  simp only [trailFalsified, List.any_eq_true] at h
  obtain ⟨l, hl, hlf⟩ := h
  have h1 : satLit a l = true := hag l hl
  have h2 : satLit a l = false := satLit_eq_false_of_isFalse hag hlf
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- A falsified clause and an agreeing assignment cannot both stand. -/
theorem not_satClause_of_clauseFalsified {a : Assign} {t : List Lit} {c : Clause}
    (hag : agree a t) (h : clauseFalsified t c = true) : satClause a c = false := by
  rw [satClause_eq_false_iff]
  intro l hl
  have : isFalse t l = true := by
    simp only [clauseFalsified, List.all_eq_true] at h
    exact h l hl
  exact satLit_eq_false_of_isFalse hag this

/-- The unit rule is sound: if every other literal of a clause of `f` is false
under an agreeing trail, the remaining one is true. -/
theorem satLit_of_isUnitOn {a : Assign} {f : Formula} {t : List Lit}
    {c : Clause} {l : Lit}
    (hf : satFormula a f = true) (hc : c ∈ f) (hag : agree a t)
    (h : isUnitOn t c l = true) : satLit a l = true := by
  have hrest : ∀ l' ∈ c, l' = l ∨ isFalse t l' = true := by
    simp only [isUnitOn, Bool.and_eq_true, List.all_eq_true] at h
    intro l' hl'
    have := h.2 l' hl'
    simpa using this
  obtain ⟨l', hl'c, hl't⟩ := satClause_eq_true_iff.mp (satClause_of_satFormula hf hc)
  rcases hrest l' hl'c with heq | hfalse
  · exact heq ▸ hl't
  · exact absurd hl't (by rw [satLit_eq_false_of_isFalse hag hfalse]; simp)

/-! ### Finding work

Both searches are written out by hand rather than through `List.findSome?` so
that their specifications are one induction each and depend on nothing. -/

/-- The first clause of `f` that the trail refutes. -/
def findConflict (t : List Lit) : Formula → Option Clause
  | [] => none
  | c :: rest => if clauseFalsified t c then some c else findConflict t rest

/-- The first literal of `c` that `c` forces under `t`. -/
def findUnitLit (t : List Lit) (c : Clause) : List Lit → Option Lit
  | [] => none
  | l :: rest => if isUnitOn t c l then some l else findUnitLit t c rest

/-- The first forced literal anywhere in `f`, with the clause forcing it. -/
def findUnit (t : List Lit) : Formula → Option (Clause × Lit)
  | [] => none
  | c :: rest =>
      match findUnitLit t c c with
      | some l => some (c, l)
      | none => findUnit t rest

theorem findConflict_spec {t : List Lit} :
    ∀ {f : Formula} {c : Clause}, findConflict t f = some c →
      c ∈ f ∧ clauseFalsified t c = true := by
  intro f
  induction f with
  | nil => intro c h; simp [findConflict] at h
  | cons d rest ih =>
      intro c h
      simp only [findConflict] at h
      split at h
      · next hd =>
          have hcd : d = c := by simpa using h
          subst hcd
          exact ⟨by simp, hd⟩
      · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

theorem findUnitLit_spec {t : List Lit} {c : Clause} :
    ∀ {ls : List Lit} {l : Lit}, findUnitLit t c ls = some l → isUnitOn t c l = true := by
  intro ls
  induction ls with
  | nil => intro l h; simp [findUnitLit] at h
  | cons x rest ih =>
      intro l h
      simp only [findUnitLit] at h
      split at h
      · next hx => have : l = x := by simpa using h.symm
                   exact this ▸ hx
      · exact ih h

theorem findUnit_spec {t : List Lit} :
    ∀ {f : Formula} {c : Clause} {l : Lit}, findUnit t f = some (c, l) →
      c ∈ f ∧ isUnitOn t c l = true := by
  intro f
  induction f with
  | nil => intro c l h; simp [findUnit] at h
  | cons d rest ih =>
      intro c l h
      simp only [findUnit] at h
      split at h
      · next x hx =>
          have hp : (d, x) = (c, l) := by simpa using h
          have hc : d = c := congrArg Prod.fst hp
          have hl : x = l := congrArg Prod.snd hp
          subst hc; subst hl
          exact ⟨by simp, findUnitLit_spec hx⟩
      · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

/-! ### The engine

Propagation is bounded by fuel. Running out returns the trail unchanged, which
is a *refusal to claim a conflict*, so the bound can only cause a rejection and
never an acceptance — soundness does not depend on the fuel being generous.
Whether it is generous enough is a completeness question, and the executable
tests in `Ratified.Examples` are where that is answered. -/

/-- Propagate to fixpoint or until the fuel runs out. `none` means a conflict
was reached. -/
def propagate (f : Formula) : Nat → List Lit → Option (List Lit)
  | 0, t => some t
  | n + 1, t =>
      if trailFalsified t then none
      else
        match findConflict t f with
        | some _ => none
        | none =>
            match findUnit t f with
            | some (_, l) => propagate f n (l :: t)
            | none => some t

/-- **Propagation soundness.** If propagation reaches a conflict from `t`, then
no assignment both satisfies `f` and agrees with `t`.

Everything downstream is an application of this theorem. -/
theorem propagate_ne_none {a : Assign} {f : Formula} (hf : satFormula a f = true) :
    ∀ (n : Nat) (t : List Lit), agree a t → propagate f n t ≠ none := by
  intro n
  induction n with
  | zero => intro t _; simp [propagate]
  | succ n ih =>
      intro t hag
      simp only [propagate]
      split
      · -- the trail contradicts itself, so nothing agrees with it
        next htf => exact fun _ => not_agree_of_trailFalsified hag htf
      · split
        · -- a clause of `f` is falsified, but `a` satisfies every clause of `f`
          next c hc =>
            refine fun _ => ?_
            obtain ⟨hcf, hfal⟩ := findConflict_spec hc
            have h1 := satClause_of_satFormula hf hcf
            have h2 := not_satClause_of_clauseFalsified hag hfal
            rw [h1] at h2
            exact Bool.noConfusion h2
        · split
          · -- a forced literal: it is true under `a`, so the longer trail still agrees
            next p hp =>
              obtain ⟨c, l⟩ := p
              obtain ⟨hcf, hunit⟩ := findUnit_spec hp
              exact ih _ (agree_cons (satLit_of_isUnitOn hf hcf hag hunit) hag)
          · simp

/-! ### Progress

Soundness never needed to know that propagation makes progress -- running out of
fuel refuses to claim a conflict, so a short bound costs completeness and nothing
else. But the *reason* the bound is finite was, until here, only a comment on
`fuelFor`: each step assigns a variable that was not assigned before, so no
variable is ever assigned twice.

That claim is load-bearing for anyone deciding what fuel to pass, so it is proved
rather than asserted. -/

/-- The variables the trail has an opinion about. -/
def trailVars (t : List Lit) : List Nat := t.map Lit.var

/-- A forced literal is always on a fresh variable.

`isUnitOn` requires the literal to be unassigned, and being unassigned means
neither it nor its complement is on the trail -- which, since those are the only
two literals on that variable, means the variable is absent entirely. -/
theorem findUnit_var_fresh {t : List Lit} {f : Formula} {c : Clause} {l : Lit}
    (h : findUnit t f = some (c, l)) : l.var ∉ trailVars t := by
  have hunit := (findUnit_spec h).2
  simp only [isUnitOn, Bool.and_eq_true] at hunit
  have hun := hunit.1.2
  simp only [isUnassigned, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at hun
  intro hmem
  obtain ⟨x, hx, hxv⟩ := List.mem_map.mp hmem
  rcases Lit.eq_or_eq_negate hxv with rfl | rfl
  · exact hun.1 hx
  · exact hun.2 hx

/-- **Propagation assigns each variable at most once.** The trail it returns
never mentions a variable twice, so the number of distinct variables in the
instance bounds the number of steps -- which is why a finite fuel exists at
all. -/
theorem propagate_nodup {f : Formula} :
    ∀ (n : Nat) (t t' : List Lit), (trailVars t).Nodup →
      propagate f n t = some t' → (trailVars t').Nodup := by
  intro n
  induction n with
  | zero =>
      intro t t' hnd h
      simp only [propagate, Option.some.injEq] at h
      exact h ▸ hnd
  | succ n ih =>
      intro t t' hnd h
      simp only [propagate] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · next cl li hp =>
              exact ih (li :: t) t' (List.nodup_cons.mpr ⟨findUnit_var_fresh hp, hnd⟩) h
          · simp only [Option.some.injEq] at h
            exact h ▸ hnd

end Ratified
