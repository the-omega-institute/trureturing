/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Counting and evaluating perfect pairings of finite label sets. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PartialPairingPolynomial
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-! Cardinality and evaluations of finite perfect pairings. -/

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

/-- A perfect pairing has half as many edges as covered labels. -/
theorem IsPerfectPairing.card {U : Finset α} {P : Finset (Finset α)}
    (hP : IsPerfectPairing U P) : U.card = 2 * P.card := by
  rw [← hP.2]
  exact pairingSupport_card hP.1

/-- Rank-one edge weights have the same product on every perfect pairing. -/
theorem finitePairingPolynomial_rankOne (U : Finset α) (c : Finset α → ℝ)
    (x : α → ℝ) (hc : ∀ e, e.card = 2 → c e = ∏ i ∈ e, x i) :
    finitePairingPolynomial U c =
      (((Finset.univ : Finset (Finset (Finset α))).filter
        (IsPerfectPairing U)).card : ℝ) * ∏ i ∈ U, x i := by
  unfold finitePairingPolynomial
  have hprod (P : Finset (Finset α)) (hP : IsPerfectPairing U P) :
      (∏ e ∈ P, c e) = ∏ i ∈ U, x i := by
    rw [Finset.prod_congr rfl (fun e he => hc e (hP.1.1 e he))]
    have h := Finset.prod_biUnion (f := x) hP.1.2.1
    change (∏ i ∈ pairingSupport P, x i) = ∏ e ∈ P, ∏ i ∈ e, x i at h
    rw [hP.2] at h
    exact h.symm
  rw [Finset.sum_congr rfl (fun P hP => hprod P (Finset.mem_filter.mp hP).2)]
  simp

/-- Constant edge weights contribute one power per edge of a perfect pairing. -/
theorem finitePairingPolynomial_const (U : Finset α) (c : Finset α → ℝ)
    (κ : ℝ) (hc : ∀ e, e.card = 2 → c e = κ) :
    finitePairingPolynomial U c =
      (((Finset.univ : Finset (Finset (Finset α))).filter
        (IsPerfectPairing U)).card : ℝ) * κ ^ (U.card / 2) := by
  unfold finitePairingPolynomial
  have hprod (P : Finset (Finset α)) (hP : IsPerfectPairing U P) :
      (∏ e ∈ P, c e) = κ ^ (U.card / 2) := by
    rw [Finset.prod_congr rfl (fun e he => hc e (hP.1.1 e he))]
    have hcard : P.card = U.card / 2 := by rw [hP.card]; omega
    simp [hcard]
  rw [Finset.sum_congr rfl (fun P hP => hprod P (Finset.mem_filter.mp hP).2)]
  simp

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
