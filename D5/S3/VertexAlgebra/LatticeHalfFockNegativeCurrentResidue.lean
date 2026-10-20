/- GID: D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete ordered negative-current residue convolution on actual native fields. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

/-! Complete ordered negative-current residues on the original actual tensor module. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection
open scoped BigOperators

noncomputable section

/-- Both ordered current products, with the signed outer residue power. -/
def currentResidue (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (F : NativeField D hu) (gamma r t : ℤ) (x : ActualTensor D hu) :
    ActualTensor D hu :=
  (∑ᶠ l : ℕ, ((-1 : ℂ) ^ l * Ring.choose (r : ℂ) l) •
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (r - l)
      (F.coeff (-2 * (t + l) - gamma - 2) x)) -
  (-1 : ℂ) ^ r •
    ∑ᶠ l : ℕ, ((-1 : ℂ) ^ l * Ring.choose (r : ℂ) l) •
      F.coeff (-2 * (r + t - l) - gamma - 2)
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i l x)

/- proof_shape: current_residue_left_finite: content
   admission_basis: escape-witness
   escape_witness: A bound from the order of F x kills the left ordered
   summand before the current acts; negative_residue_modes uses its image. -/
theorem current_residue_left_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (F : NativeField D hu) (gamma r t : ℤ)
    (x : ActualTensor D hu) :
    Function.HasFiniteSupport (fun l : ℕ =>
      ((-1 : ℂ) ^ l * Ring.choose (r : ℂ) l) •
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (r - l)
          (F.coeff (-2 * (t + l) - gamma - 2) x)) := by
  classical
  let O := ((HahnModule.of ℂ).symm (F x)).order
  refine (Finset.range ((-2 * t - gamma - 2 - O).toNat + 1)).finite_toSet.subset ?_
  intro l hl
  by_contra outside
  have low : -2 * (t + (l : ℤ)) - gamma - 2 < O := by
    simp only [Finset.mem_coe, Finset.mem_range] at outside
    omega
  have zero : F.coeff (-2 * (t + (l : ℤ)) - gamma - 2) x = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_order low
  exact hl (by simp only [zero, map_zero, smul_zero])

/- proof_shape: current_residue_right_finite: bind-only
   consumer: negative_residue_modes distributes the outer signed scalar using
   this actual-input support obtained from tensor_current_truncation. -/
theorem current_residue_right_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (F : NativeField D hu) (gamma r t : ℤ)
    (x : ActualTensor D hu) :
    Function.HasFiniteSupport (fun l : ℕ =>
      ((-1 : ℂ) ^ l * Ring.choose (r : ℂ) l) •
        F.coeff (-2 * (r + t - l) - gamma - 2)
          (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i l x)) := by
  classical
  obtain ⟨C, hC⟩ := LatticeHalfFock.tensor_current_truncation D (ActualGround D hu) x
  refine (Finset.range C).finite_toSet.subset ?_
  intro l hl
  by_contra outside
  have zero := hC i l (by simpa only [Finset.mem_coe, Finset.mem_range,
    not_lt, Nat.cast_le] using outside)
  exact hl (by simp only [zero, map_zero, smul_zero])

private def normalKernel (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (F : NativeField D hu) (gamma v : ℤ) (x : ActualTensor D hu) (q : ℤ) :
    ActualTensor D hu :=
  if q < 0 then
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
      (F.coeff (-2 * (v - q) - gamma - 2) x)
  else F.coeff (-2 * (v - q) - gamma - 2)
    (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x)

private theorem normalKernel_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (F : NativeField D hu) (gamma v : ℤ) (x : ActualTensor D hu) :
    Function.HasFiniteSupport (normalKernel D hu i F gamma v x) := by
  classical
  obtain ⟨C, hC⟩ := LatticeHalfFock.tensor_current_truncation D (ActualGround D hu) x
  let O := ((HahnModule.of ℂ).symm (F x)).order
  let L := min 0 (O + 2 * v + gamma + 2)
  refine (Finset.Icc L (C : ℤ)).finite_toSet.subset ?_
  intro q hq
  simp only [Finset.mem_coe, Finset.mem_Icc]
  by_cases neg : q < 0
  · refine ⟨?_, by omega⟩
    by_contra low
    have zero : F.coeff (-2 * (v - q) - gamma - 2) x = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_order (by dsimp [L, O] at low ⊢; omega)
    exact hq (by simp only [normalKernel, ite_eq_left neg, zero, map_zero])
  · refine ⟨by dsimp [L]; omega, ?_⟩
    by_contra high
    exact hq (by simp only [normalKernel, ite_eq_right neg, hC i q (by omega), map_zero])

/- proof_shape: reindex_supported_nat: bind-only
   consumer: negative_residue_modes, for both ordered mode ranges. -/
private theorem reindex_supported_nat {W : Type*} [AddCommGroup W]
    (f : ℤ → W) (g : ℕ → ℤ) (inj : Function.Injective g)
    (supp : Function.support f ⊆ Set.range g) :
    (∑ᶠ q : ℤ, f q) = ∑ᶠ l : ℕ, f (g l) := by
  have sets : Set.range g ∩ Function.support f = Set.univ ∩ Function.support f := by
    rw [Set.inter_eq_right.mpr supp, Set.univ_inter]
  rw [← finsum_mem_univ (f := f), ← finsum_mem_inter_support_eq f _ _ sets,
    finsum_mem_range inj]

set_option maxHeartbeats 2000000 in
private theorem negative_residue_modes (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (F : NativeField D hu) (gamma : ℤ) (h : ℕ) (t : ℤ)
    (x : ActualTensor D hu) :
    currentResidue D hu i F gamma (-(h : ℤ) - 1) t x =
      ∑ᶠ q : ℤ, Ring.choose (-(q : ℂ) - 1) h •
        normalKernel D hu i F gamma (t - h - 1) x q := by
  classical
  let K := normalKernel D hu i F gamma (t - h - 1) x
  let a (q : ℤ) : ActualTensor D hu :=
    if q < 0 then Ring.choose (-(q : ℂ) - 1) h • K q else 0
  let b (q : ℤ) : ActualTensor D hu :=
    if q < 0 then 0 else Ring.choose (-(q : ℂ) - 1) h • K q
  have leftSupport : Function.support a ⊆ Set.range (fun l : ℕ => -(h : ℤ) - 1 - l) := by
      intro q hq
      have neg : q < 0 := by by_contra hn; exact hq (by simp [a, hn])
      have le : q ≤ -(h : ℤ) - 1 := by
        by_contra hn
        have top : -(q : ℂ) - 1 = (((-q - 1).toNat : ℕ) : ℂ) := by
          have cast := congrArg (fun z : ℤ => (z : ℂ))
            (Int.toNat_of_nonneg (show 0 ≤ -q - 1 by omega))
          simpa only [Int.cast_natCast, Int.cast_sub, Int.cast_neg, Int.cast_one]
            using cast.symm
        have zero : Ring.choose (-(q : ℂ) - 1) h = 0 := by
          rw [top, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
        exact hq (by simp [a, neg, zero])
      refine ⟨(-(h : ℤ) - 1 - q).toNat, ?_⟩
      dsimp only
      rw [Int.toNat_of_nonneg (by omega)]
      omega
  have left : (∑ᶠ q : ℤ, a q) = ∑ᶠ l : ℕ, a (-(h : ℤ) - 1 - l) :=
    reindex_supported_nat a _ (by intro l l' eq; dsimp only at eq; omega) leftSupport
  have right : (∑ᶠ q : ℤ, b q) = ∑ᶠ l : ℕ, b l := by
    apply reindex_supported_nat
    · exact Nat.cast_injective
    · intro q hq
      have pos : 0 ≤ q := by by_contra hn; exact hq (by simp [b, show q < 0 by omega])
      exact ⟨q.toNat, Int.toNat_of_nonneg pos⟩
  have square (l : ℕ) : (-1 : ℂ) ^ l * (-1 : ℂ) ^ l = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have weight (l : ℕ) : (-1 : ℂ) ^ l * Ring.choose (-(h : ℂ) - 1) l =
      ((h + l).choose h : ℂ) := by
    rw [show -(h : ℂ) - 1 = -((h : ℂ) + 1) by ring, Ring.choose_neg,
      show (h : ℂ) + 1 + l - 1 = ((h + l : ℕ) : ℂ) by push_cast; ring,
      Ring.choose_natCast]
    simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]
    rw [← mul_assoc, square, one_mul, ← Nat.choose_symm_add]
  have sign : -((-1 : ℂ) ^ (-(h : ℤ) - 1)) = (-1 : ℂ) ^ h := by
    rw [show -(h : ℤ) - 1 = -((h + 1 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast, ← inv_pow]
    norm_num [pow_succ]
  have leftTerm (l : ℕ) : a (-(h : ℤ) - 1 - l) =
      ((-1 : ℂ) ^ l * Ring.choose ((-(h : ℤ) - 1 : ℤ) : ℂ) l) •
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (-(h : ℤ) - 1 - l)
          (F.coeff (-2 * (t + l) - gamma - 2) x) := by
    have qneg : -(h : ℤ) - 1 - l < 0 := by omega
    have exp : -2 * (t - h - 1 - (-(h : ℤ) - 1 - l)) - gamma - 2 =
        -2 * (t + l) - gamma - 2 := by ring
    have top : -((-(h : ℤ) - 1 - l : ℤ) : ℂ) - 1 = ((h + l : ℕ) : ℂ) := by
      push_cast; ring
    simp only [a, K, normalKernel, ite_eq_left qneg, exp]
    rw [top, Ring.choose_natCast]
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one, weight]
  have fl := current_residue_left_finite D hu i F gamma (-(h : ℤ) - 1) t x
  have fa : Function.HasFiniteSupport a := by
    refine (fl.image (fun l : ℕ => -(h : ℤ) - 1 - l)).subset ?_
    intro q hq
    obtain ⟨l, rfl⟩ := leftSupport hq
    exact ⟨l, by simpa only [Function.mem_support, ← leftTerm l] using hq, rfl⟩
  have finite := (normalKernel_finite D hu i F gamma (t - h - 1) x).smul_right
    (fun q : ℤ => Ring.choose (-(q : ℂ) - 1) h)
  have fb : Function.HasFiniteSupport b := finite.subset (by
    intro q hq
    by_cases neg : q < 0
    · exact (hq (by simp [b, neg])).elim
    · simpa only [Function.mem_support, b, ite_eq_right neg, Pi.smul_apply', K] using hq)
  have split : (∑ᶠ q : ℤ, Ring.choose (-(q : ℂ) - 1) h • K q) =
      (∑ᶠ q : ℤ, a q) + ∑ᶠ q : ℤ, b q := by
    rw [← finsum_add_distrib fa fb]
    apply finsum_congr
    intro q
    by_cases neg : q < 0 <;> simp [a, b, neg]
  rw [split, left, right, currentResidue, sub_eq_add_neg, ← neg_smul, sign,
    smul_finsum' _ (current_residue_right_finite D hu i F gamma (-(h : ℤ) - 1) t x)]
  congr 1
  · exact finsum_congr (fun l => (leftTerm l).symm)
  · apply finsum_congr
    intro l
    have top : -(l : ℂ) - 1 = -((l : ℂ) + 1) := by ring
    have exp : -2 * (t - h - 1 - (l : ℤ)) - gamma - 2 =
        -2 * (-(h : ℤ) - 1 + t - l) - gamma - 2 := by ring
    simp only [b, K, normalKernel, ite_eq_right (show ¬ (l : ℤ) < 0 by omega), exp,
      Int.cast_natCast, Int.cast_sub, Int.cast_neg, Int.cast_one]
    rw [top, Ring.choose_neg,
      show (l : ℂ) + 1 + h - 1 = ((h + l : ℕ) : ℂ) by push_cast; ring,
      Ring.choose_natCast]
    simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast,
      smul_smul, weight]

/- proof_shape: jet_vandermonde: bind-only
   consumer: singleton_negative_current_residue, inside the actual finite
   current convolution after all pointwise support and index comparisons. -/
private theorem jet_vandermonde (d : ℕ) (q : ℤ) :
    (∑ j ∈ Finset.range (d + 1),
      halfBinomial j * Ring.choose (-(q : ℂ) - 1) (d - j)) = jetScalar d q := by
  have half (j : ℕ) : halfBinomial j = Ring.choose (-1 / 2 : ℂ) j := by
    rw [Ring.choose_eq_smul, ← Polynomial.aeval_eq_smeval, Polynomial.aeval_def,
      ← Polynomial.eval_map, descPochhammer_map, descPochhammer_eval_eq_prod_range]
    simp only [halfBinomial, smul_eq_mul, div_eq_mul_inv]
    ring
  have jet : jetScalar d q = Ring.choose (-(q : ℂ) - 3 / 2) d := by
    rw [Ring.choose_eq_smul, ← Polynomial.aeval_eq_smeval, Polynomial.aeval_def,
      ← Polynomial.eval_map, descPochhammer_map, descPochhammer_eval_eq_prod_range]
    simp only [jetScalar, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [jet, show -(q : ℂ) - 3 / 2 = -1 / 2 + (-(q : ℂ) - 1) by ring,
    Ring.add_choose_eq d (Commute.all _ _),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [half]

/- proof_shape: singleton_negative_current_residue: content
   admission_basis: escape-witness
   escape_witness: negative_residue_modes identifies both ordered residues with
   the same finite actual-input mode kernel, including vanishing prefixes.
   The finite Vandermonde then recovers the original singleton jet scalar. -/
set_option maxHeartbeats 2000000 in
/-- The complete negative-current convolution on each actual native-field input. -/
theorem singleton_negative_current_residue (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (F : NativeField D hu) (gamma k : ℤ) (x : ActualTensor D hu) :
    (singletonLinear D hu index F).coeff (-2 * k - gamma - 3) x =
      ∑ j ∈ Finset.range (sourceWeight D index), halfBinomial j •
        currentResidue D hu index.1 F gamma
          (-(sourceWeight D index : ℤ) + j) (k - j) x := by
  classical
  let K := normalKernel D hu index.1 F gamma (k - sourceWeight D index) x
  have finite : Function.HasFiniteSupport K :=
    normalKernel_finite D hu index.1 F gamma (k - sourceWeight D index) x
  have weighted (j : ℕ) : Function.HasFiniteSupport (fun q : ℤ =>
      Ring.choose (-(q : ℂ) - 1) (index.2 - j) • K q) :=
    by simpa only [Pi.smul_def'] using
      finite.smul_right (fun q : ℤ => Ring.choose (-(q : ℂ) - 1) (index.2 - j))
  have residue (j : ℕ) (hj : j ∈ Finset.range (sourceWeight D index)) :
      currentResidue D hu index.1 F gamma
        (-(sourceWeight D index : ℤ) + j) (k - j) x =
      ∑ᶠ q : ℤ, Ring.choose (-(q : ℂ) - 1) (index.2 - j) • K q := by
    have within : j ≤ index.2 := by simpa [sourceWeight] using Finset.mem_range.mp hj
    have r : -(sourceWeight D index : ℤ) + j = -((index.2 - j : ℕ) : ℤ) - 1 := by
      simp only [sourceWeight, Nat.cast_add, Nat.cast_one]
      omega
    have t : k - j - (index.2 - j : ℕ) - 1 = k - sourceWeight D index := by
      simp only [sourceWeight, Nat.cast_add, Nat.cast_one]
      omega
    rw [r, negative_residue_modes, t]
  have convolution :
      (∑ j ∈ Finset.range (sourceWeight D index), halfBinomial j •
        currentResidue D hu index.1 F gamma
          (-(sourceWeight D index : ℤ) + j) (k - j) x) =
      ∑ᶠ q : ℤ, jetScalar index.2 q • K q := by
    calc
      _ = ∑ j ∈ Finset.range (sourceWeight D index), ∑ᶠ q : ℤ,
          (halfBinomial j * Ring.choose (-(q : ℂ) - 1) (index.2 - j)) • K q := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [residue j hj, smul_finsum' _ (weighted j)]
        simp only [smul_smul]
      _ = ∑ᶠ q : ℤ, ∑ j ∈ Finset.range (sourceWeight D index),
          (halfBinomial j * Ring.choose (-(q : ℂ) - 1) (index.2 - j)) • K q :=
        sum_finsum_comm _ _ (fun j _ => by
          simpa only [Pi.smul_def'] using finite.smul_right (fun q : ℤ =>
            halfBinomial j * Ring.choose (-(q : ℂ) - 1) (index.2 - j)))
      _ = _ := by
        apply finsum_congr
        intro q
        rw [← Finset.sum_smul, sourceWeight, jet_vandermonde]
  rw [convolution]
  change (wordField D hu F [index]).coeff (-2 * k - gamma - 3) x = _
  rw [wordField_coefficient,
    finsum_curry _ (flatTerm_finite D hu F [index] (-2 * k - gamma - 3) x)]
  apply finsum_congr
  intro q
  rw [finsum_unique]
  have exponent : -2 * k - gamma - 3 + 2 * q + 2 * (index.2 : ℤ) + 3 =
      -2 * (k - sourceWeight D index - q) - gamma - 2 := by
    simp only [sourceWeight, Nat.cast_add, Nat.cast_one]
    ring
  by_cases neg : q < 0
  · simp only [flatTerm, flatCoefficient, ite_eq_left neg, jetCurrent,
      Module.End.mul_apply, LinearMap.smul_apply, K, normalKernel,
      ite_eq_left neg, exponent]
  · simp only [flatTerm, flatCoefficient, ite_eq_right neg, jetCurrent,
      Module.End.mul_apply, LinearMap.smul_apply, map_smul, K, normalKernel,
      ite_eq_right neg, exponent]

end
end D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField
