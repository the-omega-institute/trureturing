/- GID: D5/S3/Constants/Irrationality/TwoFacedPrivilege
   generality: I
   mirror-B: D5/B/S3/Constants/Irrationality/TwoFacedPrivilege
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deficit integrality holds on two faces and fails to transfer to three. -/

import D5.S1.Deficit.DeficitInteger
import D5.S3.Constants.Irrationality.CubicConjugateTrace

/- Library-search audit trail (2026-08-18):
   * Both sides existed and neither is restated.  The quadratic deficit's
     integrality is `D5.S1.Deficit.deficit_integer`, whose first conjunct is the
     agreement of the expanding and contracting faces.  The cubic separation is
     `cubic_trace_is_not_carried_by_the_perron_root`, landed alongside this.
   * What did not exist is any statement putting them together, so the source's
     claim that integrality is a privilege of the two-faced structure had no
     formal counterpart even though both halves were proved.
   * Building the cubic deficit itself would need an integer-indexed naming
     layer that does not exist; issue 2446 records that cost.  This states the
     contrast without it. -/

namespace D5.S3.Constants.Irrationality.TwoFacedPrivilege

open D5.S1.Deficit
open D5.S3.Constants.Irrationality.CubicConjugateTrace
open D5.S0.Tower.Tribonacci.Values

local notation "t" => tribonacciConstant

/-- On two faces the deficit is an integer, and the reason is that the expanding
and contracting readings agree: the conjugate set is exhausted by those two, so
the irrational parts cancel. -/
theorem quadratic_deficit_is_integral (v₁ v₂ : Nat) :
    deficit v₁ v₂ = deficitContraction v₁ v₂ ∧
      ∃ z : Int, deficit v₁ v₂ = (z : Real) :=
  ⟨(deficit_integer v₁ v₂).1, (deficit_integer v₁ v₂).2.1⟩

/-- On three the cancellation is unavailable: the sum of the two non-Perron roots
is irrational, so the expanding root is in no rational relation with the rest. -/
theorem cubic_faces_do_not_cancel : Irrational (1 - t) :=
  conjugate_pair_sum_irrational

/-- Integrality of the deficit is a privilege of the two-faced structure. The
quadratic tower has it because its two faces are the whole conjugate set; the
cubic tower cannot, because splitting off its expanding root leaves a pair whose
sum is irrational. -/
theorem integrality_is_a_two_faced_privilege :
    (∀ v₁ v₂ : Nat,
        deficit v₁ v₂ = deficitContraction v₁ v₂ ∧
          ∃ z : Int, deficit v₁ v₂ = (z : Real)) ∧
      Irrational (1 - t) :=
  ⟨quadratic_deficit_is_integral, cubic_faces_do_not_cancel⟩

end D5.S3.Constants.Irrationality.TwoFacedPrivilege
