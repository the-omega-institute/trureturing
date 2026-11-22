/- GID: D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockFixedCyclicReduction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/LatticeHalfFockFixedCyclicReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A current after a theta-odd coefficient reduces to fixed integer modes on negative parity. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField

/-! Finite current elimination on the actual negative-parity half-Fock module. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockFixedCyclicReduction

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeHalfFock (tensorCurrent tensor_current_truncation)
open LatticeHalfFockChargedTensorCoefficients (ActualGround ActualTensor)
open LatticeHalfFockCorrectedField (correctedField correctedField_theta)
open LatticeHalfFockCurrentBorcherds
open LatticeHalfFockParityField (fixedParitySlice paritySpace)
open LatticeInvolution (FixedCarrier theta theta_neutralMode mem_fixedSpace)
open scoped BigOperators VertexOperator

noncomputable section

set_option maxHeartbeats 1000000 in
-- The finite-sum descent repeatedly elaborates dependent tensor and Hahn coefficient types.
/-- Signed current Borcherds reduces the odd coefficient class to even iterate coefficients. -/
private theorem odd_coeff_descent (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (b : Carrier D) (x : ActualTensor D hu)
    (S : Submodule ℂ (ActualTensor D hu))
    (iterates : ∀ t n : ℤ, (correctedField D hu (neutralMode D i t b)).coeff
      (-2 * n - 2) x ∈ S) (k q : ℤ) :
    tensorCurrent D (ActualGround D hu) i k
        ((correctedField D hu b).coeff (-2 * q - 3) x) ∈ S := by
  classical
  let product (k q : ℤ) : ActualTensor D hu :=
    tensorCurrent D (ActualGround D hu) i k
      ((correctedField D hu b).coeff (-2 * q - 3) x)
  let order := ((HahnModule.of ℂ).symm (correctedField D hu b x)).order
  let cutoff : ℤ := max 0 (-2 - order)
  have field_zero (q : ℤ) (hq : cutoff ≤ q) :
      (correctedField D hu b).coeff (-2 * q - 3) x = 0 := by
    have hnonneg : 0 ≤ q := (le_max_left 0 (-2 - order)).trans hq
    have hbound : -2 - order ≤ q := (le_max_right 0 (-2 - order)).trans hq
    have low : -2 * q - 3 < order := by omega
    exact HahnSeries.coeff_eq_zero_of_lt_order low
  obtain ⟨p, hp⟩ := tensor_current_truncation D (ActualGround D hu) x
  -- Keeping k universally quantified allows the next term to use k - j.
  have descend (d : ℕ) :
      ∀ q : ℤ, (cutoff - q).toNat = d → ∀ k : ℤ, product k q ∈ S := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro q hd k
      by_cases hq : cutoff ≤ q
      · dsimp only [product]
        rw [field_zero q hq, map_zero]
        exact S.zero_mem
      have distance : (d : ℤ) = cutoff - q := by
        rw [← hd]
        exact Int.toNat_of_nonneg (show 0 ≤ cutoff - q by omega)
      let r : ℤ := k - (p : ℤ)
      have hpr : (p : ℤ) + r = k := by
        dsimp only [r]
        omega
      let left := currentLeftTerm D hu i b 1 p q r x
      let first := currentRightFirstTerm D hu i b 1 p q r x
      let second := currentRightSecondTerm D hu i b 1 p q r x
      obtain ⟨hleft, _, _, law⟩ := current_borcherds D hu i b 1 p q r x
      change (∑ᶠ j : ℕ, left j) = (∑ᶠ j : ℕ, first j) - (∑ᶠ j : ℕ, second j) at law
      have left_mem : (∑ᶠ j : ℕ, left j) ∈ S := by
        rw [finsum_eq_sum left (show Function.HasFiniteSupport left from hleft)]
        apply S.sum_mem
        intro j _
        dsimp only [left, currentLeftTerm]
        apply S.smul_mem
        rw [show -2 * ((p : ℤ) + q - j) - 1 - 3 =
          -2 * ((p : ℤ) + q - j + 1) - 2 by omega]
        exact iterates (r + j) ((p : ℤ) + q - j + 1)
      have second_zero : (∑ᶠ j : ℕ, second j) = 0 := by
        apply finsum_eq_zero_of_forall_eq_zero
        intro j
        dsimp only [second, currentRightSecondTerm]
        rw [hp i ((p : ℤ) + j) (by omega)]
        simp only [map_zero, smul_zero]
      have first_support : Function.support first ⊆
          (↑(Finset.range (d + 1)) : Set ℕ) := by
        intro j hj
        by_contra outside
        simp only [Finset.mem_coe, Finset.mem_range] at outside
        have hqj : cutoff ≤ q + (j : ℤ) := by omega
        exact hj (by
          dsimp only [first, currentRightFirstTerm]
          rw [show -2 * (q + (j : ℤ)) - 1 - 2 = -2 * (q + j) - 3 by omega,
            field_zero _ hqj, map_zero, smul_zero])
      have first_zero : first 0 = product k q := by
        simp only [first, currentRightFirstTerm, product, pow_zero, Ring.choose_zero_right,
          one_mul, one_smul, Nat.cast_zero, add_zero, sub_zero, hpr]
        rw [show -2 * q - 1 - 2 = -2 * q - 3 by omega]
      have tail_mem : (∑ j ∈ Finset.range d, first (j + 1)) ∈ S := by
        apply S.sum_mem
        intro j _
        have smaller : (cutoff - (q + ((j + 1 : ℕ) : ℤ))).toNat < d := by omega
        dsimp only [first, currentRightFirstTerm]
        rw [hpr, show -2 * (q + ((j + 1 : ℕ) : ℤ)) - 1 - 2 =
          -2 * (q + ((j + 1 : ℕ) : ℤ)) - 3 by omega]
        apply S.smul_mem
        exact ih _ smaller _ rfl _
      rw [second_zero, sub_zero, finsum_eq_sum_of_support_subset _ first_support,
        Finset.sum_range_succ', first_zero] at law
      have recover : product k q =
          (∑ᶠ j : ℕ, left j) - (∑ j ∈ Finset.range d, first (j + 1)) :=
        eq_sub_iff_add_eq.mpr ((add_comm _ _).trans law.symm)
      rw [recover]
      exact S.sub_mem left_mem tail_mem
  exact descend (cutoff - q).toNat q rfl k

/-- A tensor current after a theta-odd corrected coefficient lies in the span of
the integer fixed-source mode actions on the same negative-parity input. -/
theorem current_after_odd_coeff_mem_fixedParitySlice_span
    (data : {D : LatticeData // IsUnit D.G.det})
    (i : Fin data.val.rank) (b : Carrier data.val) (hb : theta data.val b = -b)
    (k e : ℤ) (x : paritySpace data.val data.property (-1)) :
    ∃ y : paritySpace data.val data.property (-1),
      y.val = tensorCurrent data.val (ActualGround data.val data.property) i k
        ((correctedField data.val data.property b).coeff e x.val) ∧
      y ∈ Submodule.span ℂ (Set.range (fun index : FixedCarrier data.val × ℤ =>
        ((fixedParitySlice data.val data.property (-1) index.1)[[index.2]]) x)) := by
  rcases data with ⟨D, hu⟩
  let modes : Set (paritySpace D hu (-1)) := Set.range (fun index : FixedCarrier D × ℤ =>
    ((fixedParitySlice D hu (-1) index.1)[[index.2]]) x)
  let S := (Submodule.span ℂ modes).map (paritySpace D hu (-1)).subtype
  suffices h : tensorCurrent D (ActualGround D hu) i k
      ((correctedField D hu b).coeff e x.val) ∈ S by
    obtain ⟨y, hy, hval⟩ := Submodule.mem_map.mp h
    exact ⟨y, hval, hy⟩
  by_cases he : Even e
  · have h := correctedField_theta D hu b e
    simp only [hb, map_neg, Pi.neg_apply, he.neg_one_zpow, one_smul] at h
    have hvalue : -((correctedField D hu b).coeff e x.val) =
        (correctedField D hu b).coeff e x.val := by
      simpa only [LinearMap.neg_apply] using LinearMap.congr_fun h x.val
    have twice : (2 : ℂ) • (correctedField D hu b).coeff e x.val = 0 := by
      rw [two_smul]
      exact (congrArg (fun v => v + _) hvalue.symm).trans (neg_add_cancel _)
    have zero : (correctedField D hu b).coeff e x.val = 0 := by
      exact (smul_eq_zero.mp twice).resolve_left (by norm_num)
    rw [zero, map_zero]
    exact S.zero_mem
  have index : e = -2 * (-(e + 3) / 2) - 3 := by
    rw [Int.even_iff] at he
    omega
  rw [index]
  apply odd_coeff_descent D hu i b x.val S
  intro t n
  let a : FixedCarrier D := ⟨neutralMode D i t b, by
    rw [mem_fixedSpace, theta_neutralMode, hb, map_neg, neg_neg]⟩
  refine Submodule.mem_map.mpr ⟨((fixedParitySlice D hu (-1) a)[[n]]) x,
    Submodule.subset_span ⟨(a, n), rfl⟩, ?_⟩
  change (correctedField D hu a.val).coeff (2 * (-n - 1)) x.val = _
  rw [show 2 * (-n - 1) = -2 * n - 2 by omega]

end
end D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockFixedCyclicReduction
