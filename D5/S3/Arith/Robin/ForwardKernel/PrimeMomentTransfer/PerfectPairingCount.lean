/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Counting and evaluating perfect pairings of finite label sets. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PartialPairingPolynomial
import Mathlib.Data.Nat.Factorial.DoubleFactorial

open scoped BigOperators
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Disjoint two-element edges cover exactly twice their number of labels. -/
theorem pairingSupport_card {U : Finset α} {P : Finset (Finset α)}
    (hP : IsPartialPairing U P) : (pairingSupport P).card = 2 * P.card := by
  change (P.biUnion fun e => e).card = 2 * P.card
  rw [Finset.card_biUnion hP.2.1]
  rw [Finset.sum_congr rfl hP.1]
  simp [Nat.mul_comm]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
