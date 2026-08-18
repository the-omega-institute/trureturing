/- GID: D5/S1/Depth/ContinuedFractions/BinarySimplestTail
   generality: I
   mirror-B: D5/B/S1/Depth/ContinuedFractions/BinarySimplestTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One third is the binary tower's constant arm and the golden tail is its analogue. -/

import D5.S0.Tower.ConstantArms
import D5.S1.Depth.GoldenContinuedFraction
import D5.S0.Tower.MetricGeometry.RadixGridDistance

/- Library-search audit trail (2026-08-19):
   * Probe: one conjunct first, to settle the header shape before the rest.
   * Placed in the continued-fractions subdirectory: `D5/S1/Depth` already held
     twelve entries, which is the admission limit, and SL-003 rejected the
     thirteenth.  I had counted that limit deliberately a few hours earlier when
     splitting another directory, and did not count it here.
   * All the provable content already exists.  `binary_arm` gives the constant
     arm of one third on the binary tower; `golden_ratio_continued_fraction`
     gives the all-ones tail.  Neither is restated.
   * The remark's fourth sentence is a numerical experiment, marked in the source
     itself as machine-checked rather than proved.  It is not represented here as
     a theorem; the repository has six covered atoms carrying such annotations,
     each covered by its provable part only. -/

namespace D5.S1.Depth.ContinuedFractions.BinarySimplestTail

open D5.S0.Tower.ConstantArms
open D5.S1.Depth.GoldenContinuedFraction
open D5.S0.Tower.MetricGeometry.RadixGridDistance

/-- One third keeps a constant normalised arm on the binary tower, at every
window: this is what makes its expansion the simplest periodic tail there. -/
theorem one_third_is_the_binary_constant_arm (Q : Nat) (hQ : 1 ≤ Q) :
    (2 : Real) ^ Q * radixDistance 2 Q (1 / 3) = 1 / 3 :=
  binary_arm Q hQ

/-- The golden ratio's all-ones continued-fraction tail is the rational tower's
counterpart of that simplest periodic tail. -/
theorem golden_tail_is_all_ones :
    (GenContFract.of Real.goldenRatio).h = 1 ∧
      ∀ n, (GenContFract.of Real.goldenRatio).s.get? n = some ⟨1, 1⟩ :=
  golden_ratio_continued_fraction

/-- And the arm is constant because three and two are coprime, which is what
keeps the champion at a fixed distance while typical points drift. -/
theorem binary_champion_arm_is_constant (Q : Nat) (hQ : 1 ≤ Q) :
    Nat.Coprime 3 2 ∧
      ∀ m : Int,
        |(1 : Real) / 3 - (m : Real) / (2 : Real) ^ Q| =
          ((|((2 ^ Q : Nat) : Int) - 3 * m| : Int) : Real) /
            (3 * (2 : Real) ^ Q) :=
  ⟨(binary_constant_arm_clauses Q hQ).1, (binary_constant_arm_clauses Q hQ).2.1⟩

/-- The remark's provable content: one third is the binary tower's constant arm,
the golden tail is the rational tower's counterpart, and the arm is constant for
an arithmetic reason: every point of the binary grid sits at a distance the
numerator of one third forces, which is why the champion's arm does not drift.

An earlier draft of this conjunct kept only `Nat.Coprime 3 2`, which `decide`
settles and which mentions no window at all — a universally quantified constant
dressed as content. The distance formula is the content; coprimality is why it
holds.

The remark's fourth sentence — that the normalised distance of a random point is
near-uniform on the unit interval's lower half, with liminf almost surely zero —
is a numerical experiment, marked as machine-checked in the source rather than
proved. It is deliberately absent here. -/
theorem binary_simplest_tail_package :
    (∀ Q : Nat, 1 ≤ Q → (2 : Real) ^ Q * radixDistance 2 Q (1 / 3) = 1 / 3) ∧
      ((GenContFract.of Real.goldenRatio).h = 1 ∧
        ∀ n, (GenContFract.of Real.goldenRatio).s.get? n = some ⟨1, 1⟩) ∧
      ∀ Q : Nat, 1 ≤ Q → ∀ m : Int,
        |(1 : Real) / 3 - (m : Real) / (2 : Real) ^ Q| =
          ((|((2 ^ Q : Nat) : Int) - 3 * m| : Int) : Real) /
            (3 * (2 : Real) ^ Q) :=
  ⟨fun Q hQ => one_third_is_the_binary_constant_arm Q hQ,
    golden_tail_is_all_ones,
    fun Q hQ => (binary_champion_arm_is_constant Q hQ).2⟩

end D5.S1.Depth.ContinuedFractions.BinarySimplestTail
