/- GID: D5/S3/Quantum/Algebra/StationaryGramRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/StationaryGramRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The stationary finite-box Gram recurrence bounds matrix nullity. -/

import D5.S3.Quantum.Algebra.RectangularPolynomialNullity
import D5.S1.Ledger.BoundedTimeSlice
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Basis.SMul

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Algebra.StationaryGramRank

open D5.S1.Ledger.BoundedTimeSlice MvPolynomial Matrix
open scoped BigOperators ComplexOrder Classical

variable {sigma : Type*} [Fintype sigma]

private def lower (a : sigma → ℕ) (i : sigma) (r : TailBox a) : TailBox a := by
  classical
  exact fun j => ⟨(r j).val - if j = i then 1 else 0,
    lt_of_le_of_lt (Nat.sub_le _ _) (r j).isLt⟩

omit [Fintype sigma] in
@[simp] private theorem lower_val (a : sigma → ℕ) (i : sigma) (r : TailBox a) (j : sigma) :
    (lower a i r j).val = (r j).val - if j = i then 1 else 0 := by
  classical
  rfl

private def loweringMatrix (a : sigma → ℕ) (i : sigma) :
    Matrix (TailBox a) (TailBox a) ℂ := by
  classical
  exact fun s r => if 0 < (r i).val then
    (Pi.single (lower a i r) 1 : TailBox a → ℂ) s else 0

private def lowering (a : sigma → ℕ) (i : sigma) :
    (TailBox a → ℂ) →ₗ[ℂ] (TailBox a → ℂ) :=
  (loweringMatrix a i).mulVecLin

private theorem lowering_single (a : sigma → ℕ) (i : sigma) (r : TailBox a) (c : ℂ) :
    lowering a i (Pi.single r c) =
      if 0 < (r i).val then Pi.single (lower a i r) c else 0 := by
  classical
  ext s
  simp [lowering, loweringMatrix, Matrix.mulVec_single, Pi.single_apply]
  split_ifs <;> simp_all

private theorem lowered_gram_entry (a : sigma → ℕ) (i : sigma)
    (B : Matrix (TailBox a) (TailBox a) ℂ) (r s : TailBox a) :
    ((loweringMatrix a i).conjTranspose * B * loweringMatrix a i) r s =
      if 0 < (r i).val ∧ 0 < (s i).val
      then B (lower a i r) (lower a i s) else 0 := by
  classical
  by_cases hr : 0 < (r i).val <;> by_cases hs : 0 < (s i).val <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, loweringMatrix, hr, hs,
      Pi.single_apply]

private theorem recurrence_quadratic_identity (a : sigma → ℕ)
    (B : Matrix (TailBox a) (TailBox a) ℂ)
    (hrec : ∀ r s : TailBox a, r ≠ 0 → s ≠ 0 →
      B r s = ∑ i, if 0 < (r i).val ∧ 0 < (s i).val
        then B (lower a i r) (lower a i s) else 0)
    (u : TailBox a → ℂ) (hu : u 0 = 0) :
    star u ⬝ᵥ (B *ᵥ u) =
      ∑ i, star (lowering a i u) ⬝ᵥ (B *ᵥ lowering a i u) := by
  classical
  let Q : Matrix (TailBox a) (TailBox a) ℂ :=
    ∑ i, (loweringMatrix a i).conjTranspose * B * loweringMatrix a i
  have hQ : ∀ r s : TailBox a, r ≠ 0 → s ≠ 0 → B r s = Q r s := by
    intro r s hr hs
    simpa only [Q, Matrix.sum_apply, lowered_gram_entry] using hrec r s hr hs
  have heq : star u ⬝ᵥ (B *ᵥ u) = star u ⬝ᵥ (Q *ᵥ u) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    by_cases hr : r = 0
    · simp [hr, hu]
    · by_cases hs : s = 0
      · simp [hs, hu]
      · rw [hQ r s hr hs]
  rw [heq]
  simp only [Q, Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [lowering, Matrix.mulVecLin_apply, star_mulVec, dotProduct_mulVec,
    vecMul_vecMul]

private theorem lowering_mem_kernel (a : sigma → ℕ)
    (B : Matrix (TailBox a) (TailBox a) ℂ) (hB : B.PosSemidef)
    (hrec : ∀ r s : TailBox a, r ≠ 0 → s ≠ 0 →
      B r s = ∑ i, if 0 < (r i).val ∧ 0 < (s i).val
        then B (lower a i r) (lower a i s) else 0)
    (u : TailBox a → ℂ) (hker : u ∈ LinearMap.ker B.mulVecLin)
    (hu : u 0 = 0) (i : sigma) :
    lowering a i u ∈ LinearMap.ker B.mulVecLin := by
  classical
  have hz : star u ⬝ᵥ (B *ᵥ u) = 0 :=
    (hB.dotProduct_mulVec_zero_iff u).mpr hker
  rw [recurrence_quadratic_identity a B hrec u hu] at hz
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) => hB.dotProduct_mulVec_nonneg (lowering a j u))).mp hz
  exact (hB.dotProduct_mulVec_zero_iff _).mp (hi i (Finset.mem_univ i))


private def boxEquiv (a : sigma → ℕ) : TailBox a ≃ {d : sigma →₀ ℕ | ∀ i, d i ≤ a i} where
  toFun r := ⟨Finsupp.equivFunOnFinite.symm (fun i => (r i).val), by
    intro i
    exact Nat.le_of_lt_succ (r i).isLt⟩
  invFun d := fun i => ⟨d.val i, Nat.lt_succ_of_le (d.property i)⟩
  left_inv r := by rfl
  right_inv d := by apply Subtype.ext; ext i; rfl

private def exponent (a : sigma → ℕ) (r : TailBox a) : sigma →₀ ℕ :=
  (boxEquiv a r).val

@[simp] private theorem exponent_apply (a : sigma → ℕ) (r : TailBox a) (i : sigma) :
    exponent a r i = (r i).val := rfl

@[simp] private theorem exponent_zero (a : sigma → ℕ) : exponent a 0 = 0 := by
  ext i
  rfl

private theorem exponent_injective (a : sigma → ℕ) : Function.Injective (exponent a) := by
  intro r s h
  apply (boxEquiv a).injective
  exact Subtype.ext h

private theorem exponent_lower (a : sigma → ℕ) (i : sigma) (r : TailBox a) :
    exponent a (lower a i r) = exponent a r - Finsupp.single i 1 := by
  ext j
  simp [Finsupp.single_apply, eq_comm]

private def rectangle (a : sigma → ℕ) : Submodule ℂ (MvPolynomial sigma ℂ) :=
  restrictSupport ℂ {d | ∀ i, d i ≤ a i}

private def boxBasis (a : sigma → ℕ) : Module.Basis (TailBox a) ℂ (rectangle a) :=
  (basisRestrictSupport ℂ {d | ∀ i, d i ≤ a i}).reindex (boxEquiv a).symm

private theorem boxBasis_val (a : sigma → ℕ) (r : TailBox a) :
    (boxBasis a r).val = monomial (exponent a r) 1 := by
  refine (congrArg Subtype.val
    ((basisRestrictSupport ℂ {d : sigma →₀ ℕ | ∀ i, d i ≤ a i}).reindex_apply
      (boxEquiv a).symm r)).trans ?_
  exact congrArg AddMonoidAlgebra.ofCoeff
    (Finsupp.supportedEquivFinsupp_symm_single (R := ℂ)
      {d : sigma →₀ ℕ | ∀ i, d i ≤ a i} (boxEquiv a r) (1 : ℂ))

private def factorialProduct (a : sigma → ℕ) (r : TailBox a) : ℂ :=
  ∏ i, (Nat.factorial (r i).val : ℂ)

private theorem factorialProduct_ne_zero (a : sigma → ℕ) (r : TailBox a) :
    factorialProduct a r ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast Nat.factorial_ne_zero (r i).val

@[simp] private theorem factorialProduct_zero (a : sigma → ℕ) : factorialProduct a 0 = 1 := by
  simp [factorialProduct]

private def scaledBasis (a : sigma → ℕ) : Module.Basis (TailBox a) ℂ (rectangle a) :=
  (boxBasis a).unitsSMul
    (fun r => (Units.mk0 (factorialProduct a r) (factorialProduct_ne_zero a r))⁻¹)

private theorem scaledBasis_val (a : sigma → ℕ) (r : TailBox a) :
    (scaledBasis a r).val = monomial (exponent a r) (factorialProduct a r)⁻¹ := by
  simp [scaledBasis, Module.Basis.unitsSMul_apply, Units.smul_def, boxBasis_val,
    smul_monomial]

private def coordinateEquiv (a : sigma → ℕ) : (TailBox a → ℂ) ≃ₗ[ℂ] rectangle a :=
  (scaledBasis a).equivFun.symm

private def polynomialMap (a : sigma → ℕ) : (TailBox a → ℂ) →ₗ[ℂ] MvPolynomial sigma ℂ :=
  (rectangle a).subtype.comp (coordinateEquiv a).toLinearMap

private theorem polynomialMap_injective (a : sigma → ℕ) : Function.Injective (polynomialMap a) :=
  Subtype.val_injective.comp (coordinateEquiv a).injective

private theorem polynomialMap_single (a : sigma → ℕ) (r : TailBox a) (c : ℂ) :
    polynomialMap a (Pi.single r c) =
      monomial (exponent a r) (c * (factorialProduct a r)⁻¹) := by
  simp [polynomialMap, coordinateEquiv, Module.Basis.equivFun_symm_apply,
    scaledBasis_val, smul_monomial]

private theorem polynomialMap_mem_rectangle (a : sigma → ℕ) (u : TailBox a → ℂ) :
    polynomialMap a u ∈ rectangle a :=
  (coordinateEquiv a u).property

private theorem factorialProduct_lower (a : sigma → ℕ) (i : sigma) (r : TailBox a)
    (hr : 0 < (r i).val) :
    factorialProduct a r = (r i).val * factorialProduct a (lower a i r) := by
  have hcoord : ∀ j, (Nat.factorial (r j).val : ℂ) =
      (if j = i then ((r i).val : ℂ) else 1) *
        (Nat.factorial (lower a i r j).val : ℂ) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [lower_val]
      exact_mod_cast (Nat.mul_factorial_pred (Nat.ne_of_gt hr)).symm
    · simp [lower_val, hji]
  unfold factorialProduct
  simp_rw [hcoord, Finset.prod_mul_distrib]
  simp

private theorem pderiv_polynomialMap_single (a : sigma → ℕ) (i : sigma)
    (r : TailBox a) (c : ℂ) :
    pderiv i (polynomialMap a (Pi.single r c)) =
      polynomialMap a (lowering a i (Pi.single r c)) := by
  rw [polynomialMap_single, pderiv_monomial, ← exponent_lower, exponent_apply,
    lowering_single]
  by_cases hr : 0 < (r i).val
  · rw [if_pos hr, polynomialMap_single, factorialProduct_lower a i r hr]
    congr 1
    have hn : ((r i).val : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
    field_simp
  · have hz : (r i).val = 0 := Nat.eq_zero_of_not_pos hr
    simp [hz]

private theorem pderiv_polynomialMap (a : sigma → ℕ) (i : sigma) (u : TailBox a → ℂ) :
    pderiv i (polynomialMap a u) = polynomialMap a (lowering a i u) := by
  have h : (pderiv i).toLinearMap.comp (polynomialMap a) =
      (polynomialMap a).comp (lowering a i) := by
    apply LinearMap.pi_ext
    intro r c
    exact pderiv_polynomialMap_single a i r c
  exact LinearMap.congr_fun h u

private theorem constantCoeff_polynomialMap (a : sigma → ℕ) (u : TailBox a → ℂ) :
    constantCoeff (polynomialMap a u) = u 0 := by
  have h : (lcoeff ℂ 0).comp (polynomialMap a) = LinearMap.proj 0 := by
    apply LinearMap.pi_ext
    intro r c
    simp only [LinearMap.comp_apply, polynomialMap_single, lcoeff_apply,
      coeff_monomial, LinearMap.proj_apply]
    have he : exponent a r = 0 ↔ r = 0 := by
      rw [← exponent_zero a]
      exact (exponent_injective a).eq_iff
    by_cases hr : r = 0
    · subst r
      simp
    · simp [he, hr, eq_comm]
  exact LinearMap.congr_fun h u


/-- A normalized positive semidefinite matrix satisfying the occupation
recurrence away from the zero index has rank at least the box cardinality
minus the largest capacity, with natural subtraction. -/
theorem stationary_gram_rank_lower_bound (a : sigma → ℕ)
    (B : Matrix (TailBox a) (TailBox a) ℂ) (hB : B.PosSemidef)
    (h00 : B 0 0 = 1)
    (hrec : ∀ r s : TailBox a, r ≠ 0 → s ≠ 0 →
      B r s = ∑ i, if 0 < (r i).val ∧ 0 < (s i).val
        then B
          (fun j => ⟨(r j).val - if j = i then 1 else 0,
            lt_of_le_of_lt (Nat.sub_le _ _) (r j).isLt⟩)
          (fun j => ⟨(s j).val - if j = i then 1 else 0,
            lt_of_le_of_lt (Nat.sub_le _ _) (s j).isLt⟩)
        else 0) :
    (∏ i, (a i + 1)) - Finset.univ.sup a ≤ B.rank := by
  let N := LinearMap.ker B.mulVecLin
  let L := N.map (polynomialMap a)
  have hconst : ∀ c : ℂ, C c ∈ L → c = 0 := by
    intro c hc
    obtain ⟨u, hu, he⟩ := hc
    have hj : polynomialMap a (Pi.single 0 c) = C c := by
      simp [polynomialMap_single]
    have hu_eq : u = Pi.single 0 c :=
      polynomialMap_injective a (he.trans hj.symm)
    have hb : B *ᵥ u = 0 := hu
    have hz := congrFun hb 0
    simpa [hu_eq, Matrix.mulVec_single, h00] using hz
  have hclosed : ∀ p ∈ L, constantCoeff p = 0 → ∀ i, pderiv i p ∈ L := by
    intro p hp hp0 i
    obtain ⟨u, hu, rfl⟩ := hp
    have hu0 : u 0 = 0 := (constantCoeff_polynomialMap a u).symm.trans hp0
    exact ⟨lowering a i u, lowering_mem_kernel a B hB hrec u hu hu0 i,
      (pderiv_polynomialMap a i u).symm⟩
  have hbox : ∀ p ∈ L, ∀ d ∈ p.support, ∀ i, d i ≤ a i := by
    intro p hp
    obtain ⟨u, _, rfl⟩ := hp
    intro d hd i
    exact (mem_restrictSupport_iff ℂ).mp (polynomialMap_mem_rectangle a u) hd i
  have hbound := RectangularPolynomialNullity.stationary_rectangular_nullity_bound
    a L hconst hclosed hbox
  have hdim : Module.finrank ℂ N = Module.finrank ℂ L :=
    (Submodule.equivMapOfInjective (polynomialMap a) (polynomialMap_injective a) N).finrank_eq
  have hrank := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  have hcard : Module.finrank ℂ (TailBox a → ℂ) = ∏ i, (a i + 1) := by
    simp [TailBox, Fintype.card_pi]
  change B.rank + Module.finrank ℂ N = Module.finrank ℂ (TailBox a → ℂ) at hrank
  rw [hcard] at hrank
  omega


end D5.S3.Quantum.Algebra.StationaryGramRank
