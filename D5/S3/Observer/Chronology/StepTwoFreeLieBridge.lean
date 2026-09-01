/- GID: D5/S3/Observer/Chronology/StepTwoFreeLieBridge
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/StepTwoFreeLieBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Degree-two chronological orientation is the universal free-Lie bracket and maps to every interpreted Lie commutator. -/

import D5.S3.Observer.Chronology.PrimitiveMagnusLog
import Mathlib.Algebra.Lie.Free
import Mathlib.Tactic

/-!
# Step-two free-Lie bridge

For an event alphabet `Event`, the universal degree-two chronological defect is
the bracket of the corresponding generators in `FreeLieAlgebra R Event`.
Swapping the two events reverses its sign, a repeated event has zero bracket,
and the universal lift to any `R`-Lie algebra sends the free bracket to the
interpreted bracket.

Together with `PrimitiveMagnusLog`, this identifies the two-event alternating
tensor and the free-Lie degree-two word as two standard realizations of the
same oriented pair.  The module does not claim a completed free Lie algebra,
a Poincare-Birkhoff-Witt filtration theorem, or convergence of an infinite
Magnus logarithm.
-/

/- Library-search audit trail (2026-09-01):
   * `PrimitiveMagnusLog` owns the tensor alternant and its chronological BCH
     law.
   * Pinned Mathlib owns `FreeLieAlgebra`, its generator map, universal lift,
     and Lie bracket functoriality.  Those owners are used directly.
   * Repository search found no D5 theorem connecting the chronological
     degree-two orientation to the universal free-Lie bracket and its lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.StepTwoFreeLieBridge

open D5.S3.Observer.Chronology.PrimitiveMagnusLog

universe u v w

variable {R : Type u} [CommRing R]
variable {Event : Type v}

/-- The universal free-Lie degree-two word attached to an ordered event pair. -/
def freeLieDegreeTwo (first second : Event) : FreeLieAlgebra R Event :=
  ⁅FreeLieAlgebra.of R first, FreeLieAlgebra.of R second⁆

/-- Reversing the event pair reverses the free-Lie orientation. -/
theorem free_lie_degree_two_swap (first second : Event) :
    freeLieDegreeTwo (R := R) second first =
      -freeLieDegreeTwo (R := R) first second := by
  simp [freeLieDegreeTwo, lie_skew]

/-- Repeating one event gives no degree-two free-Lie defect. -/
theorem free_lie_degree_two_self (event : Event) :
    freeLieDegreeTwo (R := R) event event = 0 := by
  simp [freeLieDegreeTwo]

/-- Every interpretation of the event alphabet in an `R`-Lie algebra sends
the universal degree-two word to the corresponding interpreted bracket. -/
theorem free_lie_degree_two_lift
    {L : Type w} [LieRing L] [Module R L] [LieAlgebra R L]
    (interpret : Event → L) (first second : Event) :
    FreeLieAlgebra.lift R interpret
        (freeLieDegreeTwo (R := R) first second) =
      ⁅interpret first, interpret second⁆ := by
  simp [freeLieDegreeTwo]

/-- The tensor and free-Lie realizations have the same exchange orientation. -/
theorem tensor_and_free_lie_swap_orientation
    {V : Type w} [AddCommGroup V] [Module R V]
    (embed : Event → V) (first second : Event) :
    tensorLieBracket (R := R) (embed second) (embed first) =
        -tensorLieBracket (R := R) (embed first) (embed second) ∧
      freeLieDegreeTwo (R := R) second first =
        -freeLieDegreeTwo (R := R) first second := by
  exact ⟨tensor_lie_bracket_swap _ _, free_lie_degree_two_swap _ _⟩

/-- A commuting interpreted pair annihilates the universal degree-two word
under the free-Lie lift. -/
theorem free_lie_degree_two_lift_eq_zero_of_bracket_eq_zero
    {L : Type w} [LieRing L] [Module R L] [LieAlgebra R L]
    (interpret : Event → L) (first second : Event)
    (hCommute : ⁅interpret first, interpret second⁆ = 0) :
    FreeLieAlgebra.lift R interpret
        (freeLieDegreeTwo (R := R) first second) = 0 := by
  rw [free_lie_degree_two_lift, hCommute]

example :
    freeLieDegreeTwo (R := ℤ) true true = 0 := by
  exact free_lie_degree_two_self true

#print axioms free_lie_degree_two_swap
#print axioms free_lie_degree_two_self
#print axioms free_lie_degree_two_lift
#print axioms tensor_and_free_lie_swap_orientation
#print axioms free_lie_degree_two_lift_eq_zero_of_bracket_eq_zero

end D5.S3.Observer.Chronology.StepTwoFreeLieBridge
