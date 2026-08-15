/-
The axiom audit.

A Lean development can be undermined in two quiet ways: an unfinished proof left
as `sorry`, and a `native_decide` that moves a computation out of the kernel and
into the compiler. Both are invisible in a green build and both show up in the
axiom list — as `sorryAx` and `Lean.ofReduceBool` respectively.

So the axiom list is pinned here with `#guard_msgs`, which fails the build if it
ever changes. What it currently says is that the theorems rest on `propext` and
`Quot.sound` and nothing else: no `sorry`, no compiler trust, and not even
`Classical.choice`.
-/
import Ratified.Examples

namespace Ratified

/-- info: 'Ratified.checkProof_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Ratified.checkProof_sound

/-- info: 'Ratified.no_false_accept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Ratified.no_false_accept

/-- info: 'Ratified.isRAT_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Ratified.isRAT_sound

/-- info: 'Ratified.isRUP_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Ratified.isRUP_sound

/-- info: 'Ratified.propagate_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Ratified.propagate_ne_none

/-- info: 'Ratified.F₁_unsat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Ratified.F₁_unsat

end Ratified
