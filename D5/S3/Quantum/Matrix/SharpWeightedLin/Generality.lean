/- GID: D5/S3/Quantum/Matrix/SharpWeightedLin/Generality
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/SharpWeightedLin/Generality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hermitian inertia, spectral projections, isometric compression, and ordered spectral powers. -/

import D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
import D5.S3.Quantum.Schatten.SingularValueOrder
import D5.S3.SpectralTopology.PointGapExactInertia
import D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-! General matrix analysis used by the weighted comparison. -/
noncomputable section
namespace D5.S3.Quantum.Matrix.SharpWeightedLin

section Inertia
open _root_.Matrix
open scoped ComplexOrder



open RHLinalg
open D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback

variable {n k : Type} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

private theorem roots_count (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (p : ℝ → Prop) [DecidablePred p] :
    (A.charpoly.roots.map Complex.re).countP p =
      (Finset.univ.filter fun i => p (hA.eigenvalues i)).card := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, Multiset.countP_map]
  simp only [Function.comp_apply, Complex.ofReal_re]
  rfl

private theorem block_inertia (A : Matrix n n ℂ) (B : Matrix k k ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    posIndex (hA.fromBlocks (B := (0 : Matrix n k ℂ)) (C := 0) (by simp) hB) = posIndex hA + posIndex hB ∧
      negIndex (hA.fromBlocks (B := (0 : Matrix n k ℂ)) (C := 0) (by simp) hB) = negIndex hA + negIndex hB := by
  have hroots : (fromBlocks A 0 0 B).charpoly.roots =
      A.charpoly.roots + B.charpoly.roots := by
    rw [charpoly_fromBlocks_zero₁₂, Polynomial.roots_mul]
    exact mul_ne_zero A.charpoly_monic.ne_zero B.charpoly_monic.ne_zero
  constructor
  · rw [posIndex, ← roots_count _ (hA.fromBlocks (B := (0 : Matrix n k ℂ)) (C := 0) (by simp) hB), hroots,
      Multiset.map_add, Multiset.countP_add, roots_count _ hA, roots_count _ hB]
    rfl
  · rw [negIndex, ← roots_count _ (hA.fromBlocks (B := (0 : Matrix n k ℂ)) (C := 0) (by simp) hB) (fun x : ℝ => x < 0), hroots,
      Multiset.map_add, Multiset.countP_add, roots_count _ hA, roots_count _ hB]
    rfl

/-- Eliminating the upper-left invertible Hermitian block is a congruence. -/
private theorem schur_congruence_left (A : Matrix n n ℂ) (B : Matrix n k ℂ)
    (D : Matrix k k ℂ) (hA : A.IsHermitian) (hunit : IsUnit A.det) :
    let T := fromBlocks (1 : Matrix n n ℂ) (-(A⁻¹ * B)) 0 (1 : Matrix k k ℂ)
    Tᴴ * fromBlocks A B Bᴴ D * T =
      fromBlocks A 0 0 (D - Bᴴ * A⁻¹ * B) := by
  dsimp
  have hAA : A * A⁻¹ = 1 := mul_nonsing_inv A hunit
  have hAA' : A⁻¹ * A = 1 := nonsing_inv_mul A hunit
  simp only [fromBlocks_conjTranspose, conjTranspose_one, conjTranspose_zero,
    conjTranspose_neg, conjTranspose_mul, hA.inv.eq, fromBlocks_multiply]
  apply fromBlocks_inj.mpr
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul]
  constructor
  · trivial
  constructor
  · rw [← Matrix.mul_assoc, hAA, Matrix.one_mul, neg_add_cancel]
  constructor
  · rw [Matrix.mul_assoc, hAA', Matrix.mul_one, neg_add_cancel]
  · simp [Matrix.mul_assoc, hAA', sub_eq_add_neg, add_comm]

/-- Haynsworth inertia addition over the complex field, including zero eigenvalues. -/
private theorem schur_inertia_left (A : Matrix n n ℂ) (B : Matrix n k ℂ)
    (D : Matrix k k ℂ) (hA : A.IsHermitian) (hD : D.IsHermitian)
    (hunit : IsUnit A.det) :
    let hL : (fromBlocks A B Bᴴ D).IsHermitian := hA.fromBlocks (B := B) rfl hD
    let hS : (D - Bᴴ * A⁻¹ * B).IsHermitian :=
      hD.sub (isHermitian_conjTranspose_mul_mul B hA.inv)
    posIndex hL = posIndex hA + posIndex hS ∧
      negIndex hL = negIndex hA + negIndex hS := by
  dsimp
  let T := fromBlocks (1 : Matrix n n ℂ) (-(A⁻¹ * B)) 0 (1 : Matrix k k ℂ)
  have hT : IsUnit T.det := by simp [T, det_fromBlocks_zero₂₁]
  have hi := inertia_invariant_of_isUnit_det (hA.fromBlocks (B := B) rfl hD) T hT
  have hc := schur_congruence_left A B D hA hunit
  have hb := block_inertia A (D - Bᴴ * A⁻¹ * B) hA
    (hD.sub (isHermitian_conjTranspose_mul_mul B hA.inv))
  constructor
  · have heq : posIndex (isHermitian_conjTranspose_mul_mul T
        (hA.fromBlocks (B := B) rfl hD)) =
        posIndex (hA.fromBlocks (B := (0 : Matrix n k ℂ)) (C := 0) (by simp)
          (hD.sub (isHermitian_conjTranspose_mul_mul B hA.inv))) := by
      congr 1
    omega
  · have heq : negIndex (isHermitian_conjTranspose_mul_mul T
        (hA.fromBlocks (B := B) rfl hD)) =
        negIndex (hA.fromBlocks (B := (0 : Matrix n k ℂ)) (C := 0) (by simp)
          (hD.sub (isHermitian_conjTranspose_mul_mul B hA.inv))) := by
      congr 1
    omega

/-- Eliminating the lower-right invertible Hermitian block is a congruence. -/
private theorem schur_congruence_right (A : Matrix n n ℂ) (B : Matrix n k ℂ)
    (D : Matrix k k ℂ) (hD : D.IsHermitian) (hunit : IsUnit D.det) :
    let T := fromBlocks (1 : Matrix n n ℂ) 0 (-(D⁻¹ * Bᴴ)) (1 : Matrix k k ℂ)
    Tᴴ * fromBlocks A B Bᴴ D * T =
      fromBlocks (A - B * D⁻¹ * Bᴴ) 0 0 D := by
  dsimp
  have hDD : D * D⁻¹ = 1 := mul_nonsing_inv D hunit
  have hDD' : D⁻¹ * D = 1 := nonsing_inv_mul D hunit
  simp only [fromBlocks_conjTranspose, conjTranspose_one, conjTranspose_zero,
    conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose,
    hD.inv.eq, fromBlocks_multiply]
  apply fromBlocks_inj.mpr
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul]
  constructor
  · simp [Matrix.mul_assoc, hDD', sub_eq_add_neg]
  constructor
  · rw [Matrix.mul_assoc, hDD', Matrix.mul_one, add_neg_cancel]
  constructor
  · rw [← Matrix.mul_assoc, hDD, Matrix.one_mul, add_neg_cancel]
  · trivial

/-- Haynsworth addition in the lower-right block. -/
private theorem schur_inertia_right (A : Matrix n n ℂ) (B : Matrix n k ℂ)
    (D : Matrix k k ℂ) (hA : A.IsHermitian) (hD : D.IsHermitian)
    (hunit : IsUnit D.det) :
    let hL : (fromBlocks A B Bᴴ D).IsHermitian := hA.fromBlocks (B := B) rfl hD
    let hS : (A - B * D⁻¹ * Bᴴ).IsHermitian :=
      hA.sub (by simpa using isHermitian_conjTranspose_mul_mul Bᴴ hD.inv)
    posIndex hL = posIndex hS + posIndex hD ∧
      negIndex hL = negIndex hS + negIndex hD := by
  dsimp
  let T := fromBlocks (1 : Matrix n n ℂ) 0 (-(D⁻¹ * Bᴴ)) (1 : Matrix k k ℂ)
  have hT : IsUnit T.det := by simp [T, det_fromBlocks_zero₁₂]
  have hi := inertia_invariant_of_isUnit_det (hA.fromBlocks (B := B) rfl hD) T hT
  have hc := schur_congruence_right A B D hD hunit
  have hs : (A - B * D⁻¹ * Bᴴ).IsHermitian :=
    hA.sub (by simpa using isHermitian_conjTranspose_mul_mul Bᴴ hD.inv)
  have hb := block_inertia (A - B * D⁻¹ * Bᴴ) D hs hD
  constructor
  · have heq : posIndex (isHermitian_conjTranspose_mul_mul T
        (hA.fromBlocks (B := B) rfl hD)) = posIndex (hs.fromBlocks (B := (0 : Matrix n k ℂ)) (C := 0) (by simp) hD) := by
      congr 1
    omega

  · have heq : negIndex (isHermitian_conjTranspose_mul_mul T
        (hA.fromBlocks (B := B) rfl hD)) = negIndex (hs.fromBlocks (B := (0 : Matrix n k ℂ)) (C := 0) (by simp) hD) := by
      congr 1
    omega

/-- Eigenvalues greater than or equal to zero, counted with multiplicity. -/
def nonnegIndex {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => 0 ≤ hA.eigenvalues i).card

/-- Eigenvalues less than or equal to zero, counted with multiplicity. -/
def nonposIndex {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => hA.eigenvalues i ≤ 0).card

private theorem nonnegIndex_eq_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    nonnegIndex hA = Fintype.card n - negIndex hA := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i => hA.eigenvalues i < 0)
  simp only [not_lt, Finset.card_univ] at h
  unfold nonnegIndex negIndex
  omega

private theorem nonposIndex_eq_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    nonposIndex hA = Fintype.card n - posIndex hA := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i => 0 < hA.eigenvalues i)
  simp only [not_lt, Finset.card_univ] at h
  unfold nonposIndex posIndex
  omega

/-- The finite-dimensional Birman--Schwinger inertia identity. -/
theorem positive_update_inertia (H : Matrix n n ℂ) (J : Matrix n k ℂ)
    (W : Matrix k k ℂ) (hH : H.IsHermitian) (hunit : IsUnit H.det)
    (hW : W.PosDef) :
    let hM : (H + J * W * Jᴴ).IsHermitian :=
      hH.add (by simpa using isHermitian_conjTranspose_mul_mul Jᴴ hW.isHermitian)
    let hG : (W⁻¹ + Jᴴ * H⁻¹ * J).IsHermitian :=
      hW.inv.isHermitian.add (isHermitian_conjTranspose_mul_mul J hH.inv)
    nonnegIndex hM = posIndex hH + nonposIndex hG := by
  dsimp
  let M := H + J * W * Jᴴ
  let G := W⁻¹ + Jᴴ * H⁻¹ * J
  have hM : M.IsHermitian :=
    hH.add (by simpa using isHermitian_conjTranspose_mul_mul Jᴴ hW.isHermitian)
  have hG : G.IsHermitian :=
    hW.inv.isHermitian.add (isHermitian_conjTranspose_mul_mul J hH.inv)
  have hWinvUnit : IsUnit W⁻¹ := hW.inv.isUnit
  have hDUnit : IsUnit (-W⁻¹).det :=
    (isUnit_iff_isUnit_det _).mp hWinvUnit.neg
  have hinv : (-W⁻¹)⁻¹ = -W := by
    apply Matrix.inv_eq_left_inv
    simp only [neg_mul_neg]
    exact mul_nonsing_inv W ((isUnit_iff_isUnit_det _).mp hW.isUnit)
  have hleft := schur_inertia_left H J (-W⁻¹) hH hW.inv.isHermitian.neg hunit
  have hright := schur_inertia_right H J (-W⁻¹) hH hW.inv.isHermitian.neg hDUnit
  have hSL : -W⁻¹ - Jᴴ * H⁻¹ * J = -G := by dsimp [G]; abel
  have hSR : H - J * (-W⁻¹)⁻¹ * Jᴴ = M := by
    rw [hinv]
    simp [M, Matrix.mul_neg, Matrix.neg_mul]
  have hbalance :
      negIndex hH + negIndex hG.neg = negIndex hM + negIndex hW.inv.isHermitian.neg := by
    simpa only [hSL, hSR] using hleft.2.symm.trans hright.2
  have hGneg : negIndex hG.neg = posIndex hG := by
    have h := D5.S3.SpectralTopology.FiniteSpectralLocalizer.posIndex_neg_eq_negIndex hG.neg
    simpa only [neg_neg] using h.symm
  have hWneg : negIndex hW.inv.isHermitian.neg = Fintype.card k := by
    have h := D5.S3.SpectralTopology.FiniteSpectralLocalizer.posIndex_neg_eq_negIndex
      hW.inv.isHermitian.neg
    have hp : posIndex hW.inv.isHermitian = Fintype.card k := by
      unfold posIndex
      simp [hW.inv.eigenvalues_pos]
    simpa only [neg_neg, hp] using h.symm
  have hHtotal : posIndex hH + negIndex hH = Fintype.card n := by
    rw [D5.S3.SpectralTopology.PointGapExactInertia.posIndex_add_negIndex_eq_rank hH]
    exact rank_of_isUnit H ((isUnit_iff_isUnit_det _).mpr hunit)
  have hGp := posIndex_le_card hG
  have hMn : negIndex hM ≤ Fintype.card n :=
    Finset.card_le_card (Finset.filter_subset _ _) |>.trans_eq Finset.card_univ
  rw [hGneg, hWneg] at hbalance
  change nonnegIndex hM = posIndex hH + nonposIndex hG
  rw [nonnegIndex_eq_sub, nonposIndex_eq_sub]
  omega

/-- A subspace with a nonpositive quadratic form is bounded by the nonpositive index. -/
theorem finrank_le_nonposIndex {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (U : Submodule ℂ (n → ℂ)) (hU : ∀ x ∈ U, hermForm A x ≤ 0) :
    Module.finrank ℂ U ≤ nonposIndex hA := by
  let V := LinearMap.range (hermPosPart hA).mulVecLin
  have hd : Disjoint U V := by
    rw [Submodule.disjoint_def]
    intro x hxU hxV
    by_contra hx
    have hp := posDefOn_range_hermPosPart hA x hxV hx
    have hn := hU x hxU
    linarith
  have hdim := Submodule.finrank_add_finrank_le_of_disjoint hd
  have hV : Module.finrank ℂ V = posIndex hA := finrank_range_hermPosPart hA
  rw [hV] at hdim
  have hdim' : Module.finrank ℂ U + posIndex hA ≤ Fintype.card n := by
    simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one] using hdim
  rw [nonposIndex_eq_sub]
  omega
end Inertia

section RankReduction
open _root_.Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Congruencing a spectral lower bound by the inverse power and applying
Löwner–Heinz gives the smaller positive matrix used in rank reduction. -/
theorem rank_reduction_order {X Y E : Matrix ι ι ℂ}
    (hX : X.PosDef) (hY : Y.PosSemidef) {a b : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b)
    (hE : E ≤ CFC.rpow X (1 / (2 * b)) * CFC.rpow Y (1 / a) *
      CFC.rpow X (1 / (2 * b))) :
    CFC.rpow (CFC.rpow X (-(1 / (2 * b))) * E *
      CFC.rpow X (-(1 / (2 * b)))) a ≤ Y := by
  let P := CFC.rpow X (1 / (2 * b))
  let R := CFC.rpow X (-(1 / (2 * b)))
  let Q := CFC.rpow Y (1 / a)
  have hRP : R * P = 1 := CFC.rpow_neg_mul_rpow _ hX.isStrictlyPositive
  have hPR : P * R = 1 := CFC.rpow_mul_rpow_neg _ hX.isStrictlyPositive
  have hR : 0 ≤ R := CFC.rpow_nonneg
  have hc : R * E * R ≤ R * (P * Q * P) * R :=
    conjugate_le_conjugate_of_nonneg hE hR
  have heq : R * (P * Q * P) * R = Q := by
    calc
      _ = (R * P) * Q * (P * R) := by noncomm_ring
      _ = Q := by rw [hRP, hPR, one_mul, mul_one]
  rw [heq] at hc
  have hp := CFC.rpow_le_rpow (show a ∈ Set.Icc (0 : ℝ) 1 from ⟨ha.le, ha1⟩) hc
  have hQ : CFC.rpow Q a = Y := by
    dsimp [Q]
    rw [CFC.rpow_rpow_of_exponent_nonneg Y (1 / a) a (by positivity) ha.le hY.nonneg,
      one_div_mul_cancel ha.ne', CFC.rpow_one Y hY.nonneg]
  change CFC.rpow (R * E * R) a ≤ CFC.rpow Q a at hp
  rw [hQ] at hp
  exact hp

/-- The congruenced projection is its own generalized inverse relative to
the full positive power. This identifies its compression on its range. -/
private theorem rank_reduction_support_identity {X E : Matrix ι ι ℂ}
    (hX : X.PosDef) (hE : E * E = E) {b : ℝ} (hb : 0 < b) :
    let R := CFC.rpow X (-(1 / (2 * b)))
    let K := R * E * R
    K * CFC.rpow X (1 / b) * K = K := by
  let R := CFC.rpow X (-(1 / (2 * b)))
  have hmiddle : R * CFC.rpow X (1 / b) * R = 1 := by
    dsimp [R]
    rw [← CFC.rpow_add hX.isUnit, ← CFC.rpow_add hX.isUnit]
    have he : -(1 / (2 * b)) + 1 / b + -(1 / (2 * b)) = 0 := by
      field_simp
      <;> ring
    rw [he, CFC.rpow_zero X hX.posSemidef.nonneg]
  change (R * E * R) * CFC.rpow X (1 / b) * (R * E * R) = R * E * R
  calc
    _ = R * E * (R * CFC.rpow X (1 / b) * R) * E * R := by noncomm_ring
    _ = R * (E * E) * R := by rw [hmiddle]; noncomm_ring
    _ = R * E * R := by rw [hE]
end RankReduction

section Compression
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

local instance compressionPow {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Pow (Matrix ι ι ℂ) ℝ := ⟨CFC.rpow⟩

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

/-- Positive powers commute with embedding a positive matrix into an isometric range.
The exponent is strictly positive so that the orthogonal complement contributes zero. -/
private theorem rpow_isometry_conjugate (J : Matrix n k ℂ) (hJ : Jᴴ * J = 1)
    (D : Matrix k k ℂ) (hD : D.PosSemidef) {a : ℝ} (ha : 0 < a) :
    CFC.rpow (J * D * Jᴴ) a = J * CFC.rpow D a * Jᴴ := by
  let φ : Matrix k k ℂ →⋆ₙₐ[ℝ] Matrix n n ℂ :=
    { toFun := fun A => J * A * Jᴴ
      map_zero' := by simp
      map_add' := by intro A B; simp only [Matrix.mul_add, Matrix.add_mul]
      map_mul' := by
        intro A B
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Jᴴ, hJ, Matrix.one_mul]
      map_smul' := by intro r A; simp
      map_star' := by
        intro A
        simp [Matrix.star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc] }
  have hJD : (J * D * Jᴴ).PosSemidef := hD.mul_mul_conjTranspose_same J
  have hm := φ.map_cfcₙ (fun x : ℝ => x ^ a) D
    (by exact (Real.continuous_rpow_const ha.le).continuousOn)
    (by simp [ha.ne']) (by dsimp [φ]; fun_prop)
    hD.isHermitian.isSelfAdjoint hJD.isHermitian.isSelfAdjoint
  have hleft : CFC.rpow D a = cfcₙ (fun x : ℝ => x ^ a) D := by
    have h := CFC.rpow_eq_cfc_real (y := a) hD.nonneg
    change CFC.rpow D a = cfc (fun x : ℝ => x ^ a) D at h
    exact h.trans (cfcₙ_eq_cfc (R := ℝ) (A := Matrix k k ℂ) (p := IsSelfAdjoint)
      (hf := (Real.continuous_rpow_const ha.le).continuousOn)
      (hf0 := by simp [ha.ne'])).symm
  have hright : CFC.rpow (J * D * Jᴴ) a =
      cfcₙ (fun x : ℝ => x ^ a) (J * D * Jᴴ) := by
    have h := CFC.rpow_eq_cfc_real (y := a) hJD.nonneg
    change CFC.rpow (J * D * Jᴴ) a = cfc (fun x : ℝ => x ^ a) (J * D * Jᴴ) at h
    exact h.trans (cfcₙ_eq_cfc (R := ℝ) (A := Matrix n n ℂ) (p := IsSelfAdjoint)
      (hf := (Real.continuous_rpow_const ha.le).continuousOn)
      (hf0 := by simp [ha.ne'])).symm
  rw [hleft, hright]
  exact hm.symm

/-- A positive matrix of rank `k` has a positive definite coordinate matrix on an
isometrically embedded `k` dimensional support. -/
private theorem exists_support_isometry {n k : ℕ} (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : K.PosSemidef) (hrank : K.rank = k) :
    ∃ (J : Matrix (Fin n) (Fin k) ℂ) (D : Matrix (Fin k) (Fin k) ℂ),
      Jᴴ * J = 1 ∧ D.PosDef ∧ K = J * D * Jᴴ := by
  classical
  let I := {i : Fin n // hK.isHermitian.eigenvalues i ≠ 0}
  have hcard : Fintype.card (Fin k) = Fintype.card I := by
    rw [Fintype.card_fin, ← hK.isHermitian.rank_eq_card_non_zero_eigs]
    exact hrank.symm
  let e : Fin k ≃ I := Fintype.equivOfCardEq hcard
  let U : Matrix (Fin n) (Fin n) ℂ := hK.isHermitian.eigenvectorUnitary
  let f : Fin k → Fin n := fun i => (e i).val
  let J : Matrix (Fin n) (Fin k) ℂ := U.submatrix id f
  let d : Fin k → ℂ := fun i => (hK.isHermitian.eigenvalues (f i) : ℂ)
  let D := Matrix.diagonal d
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hJ : Jᴴ * J = 1 := by
    dsimp [J]
    rw [conjTranspose_submatrix,
      ← Matrix.submatrix_mul Uᴴ U f id f Function.bijective_id]
    have hU : Uᴴ * U = 1 := hK.isHermitian.eigenvectorUnitary.2.1
    rw [hU, Matrix.submatrix_one f hf]
  have hD : D.PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    have hpos : 0 < hK.isHermitian.eigenvalues (f i) :=
      lt_of_le_of_ne (hK.eigenvalues_nonneg (f i)) (e i).property.symm
    change (0 : ℂ) < (hK.isHermitian.eigenvalues (f i) : ℂ)
    exact_mod_cast hpos
  refine ⟨J, D, hJ, hD, ?_⟩
  have hspec : K = U * Matrix.diagonal (fun i =>
      (hK.isHermitian.eigenvalues i : ℂ)) * Uᴴ := hK.isHermitian.spectral_theorem
  rw [hspec]
  change U * Matrix.diagonal (fun i => (hK.isHermitian.eigenvalues i : ℂ)) * Uᴴ =
    J * Matrix.diagonal d * Jᴴ
  ext i j
  change (∑ t, (U * Matrix.diagonal (fun i =>
    (hK.isHermitian.eigenvalues i : ℂ))) i t * star (U j t)) =
      ∑ t, (J * Matrix.diagonal d) i t * star (J j t)
  simp only [Matrix.mul_diagonal]
  let g : Fin n → ℂ := fun t => U i t * (hK.isHermitian.eigenvalues t : ℂ) * star (U j t)
  have hz : ∑ t : {t : Fin n // ¬ hK.isHermitian.eigenvalues t ≠ 0}, g t = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    have ht : hK.isHermitian.eigenvalues t = 0 := not_ne_iff.mp t.property
    simp [g, ht]
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun t => hK.isHermitian.eigenvalues t ≠ 0) g
  rw [hz, add_zero] at hs
  have he := e.sum_comp (fun t : I => g t)
  change ∑ t, g t = ∑ t, g (f t)
  exact hs.symm.trans he.symm

/-- The congruenced rank projection is the inverse of the positive compression
of `X^(1/b)` on its support; all positive powers have the corresponding formula. -/
theorem reduced_projection_compression {n k : ℕ}
    (X E : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosDef) (hE : E.PosSemidef)
    (hE2 : E * E = E) (hrank : E.rank = k)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let R := CFC.rpow X (-(1 / (2 * b)))
    let K := R * E * R
    ∃ J : Matrix (Fin n) (Fin k) ℂ,
      Jᴴ * J = 1 ∧
      let S := Jᴴ * CFC.rpow X (1 / b) * J
      S.PosDef ∧ CFC.rpow K a = J * CFC.rpow S (-a) * Jᴴ := by
  let R := CFC.rpow X (-(1 / (2 * b)))
  let K := R * E * R
  have hR : R.PosDef :=
    (hX.isStrictlyPositive.rpow X (-(1 / (2 * b)))).posDef
  have hK : K.PosSemidef := by
    simpa only [K, hR.isHermitian.eq] using hE.mul_mul_conjTranspose_same R
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have hkrank : K.rank = k := by
    dsimp [K]
    rw [Matrix.rank_mul_eq_left_of_isUnit_det R (R * E) hRdet,
      Matrix.rank_mul_eq_right_of_isUnit_det R E hRdet, hrank]
  obtain ⟨J, D, hJ, hD, hfac⟩ := exists_support_isometry K hK hkrank
  let S := Jᴴ * CFC.rpow X (1 / b) * J
  have hsupport : K * CFC.rpow X (1 / b) * K = K :=
    rank_reduction_support_identity hX hE2 hb
  have hDSD : D * S * D = D := by
    have h := congrArg (fun A => Jᴴ * A * J) hsupport
    rw [hfac] at h
    simp only [Matrix.mul_assoc] at h
    simp only [← Matrix.mul_assoc Jᴴ J, hJ, Matrix.one_mul, Matrix.mul_one] at h
    simpa only [S, Matrix.mul_assoc] using h
  have hDD : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D
    ((Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit)
  have hDD' : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D
    ((Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit)
  have hS : S = D⁻¹ := by
    calc
      S = (D⁻¹ * D) * S * (D * D⁻¹) := by rw [hDD', hDD]; simp
      _ = D⁻¹ * (D * S * D) * D⁻¹ := by simp only [Matrix.mul_assoc]
      _ = D⁻¹ * D * D⁻¹ := by rw [hDSD]
      _ = D⁻¹ := by rw [hDD', Matrix.one_mul]
  refine ⟨J, hJ, ?_, ?_⟩
  · change S.PosDef
    rw [hS]
    exact hD.inv
  · change CFC.rpow K a = J * CFC.rpow S (-a) * Jᴴ
    rw [hfac, rpow_isometry_conjugate J hJ D hD.posSemidef ha, hS]
    have hinv : D⁻¹ = CFC.rpow D (-1) := by
      rw [Matrix.nonsing_inv_eq_ringInverse]
      exact CFC.inverse_eq_rpow_neg_one hD.isStrictlyPositive
    have hpow := CFC.rpow_rpow D (-1) (-a) (by norm_num) hD.isStrictlyPositive
    change CFC.rpow (CFC.rpow D (-1)) (-a) = CFC.rpow D ((-1) * (-a)) at hpow
    rw [hinv, hpow]
    simp
end Compression

section SpectralProjection
open _root_.Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-- A spectral value at least one provides an orthogonal projection of the
corresponding initial rank below the matrix. -/
theorem spectral_lower_projection {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.PosSemidef) (j : Fin (Fintype.card (Fin n)))
    (hj : 1 ≤ hT.isHermitian.eigenvalues₀ j) :
    ∃ E : Matrix (Fin n) (Fin n) ℂ,
      E.PosSemidef ∧ E * E = E ∧ E.rank = j.val + 1 ∧ E ≤ T := by
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let U : Matrix (Fin n) (Fin n) ℂ := hT.isHermitian.eigenvectorUnitary
  let d : Fin n → ℂ := fun i => if e.symm i ≤ j then 1 else 0
  let D := diagonal d
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have hUi : IsUnit U := Unitary.isUnit_coe
  have hUd : IsUnit U.det := (isUnit_iff_isUnit_det _).mp hUi
  have hUHd : IsUnit Uᴴ.det := (isUnit_iff_isUnit_det _).mp hUi.star
  have hD : D.PosSemidef := by
    apply PosSemidef.diagonal
    intro i
    dsimp [d]
    split_ifs <;> norm_num
  have hDD : D * D = D := by
    dsimp [D]
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    dsimp [d]
    split_ifs <;> norm_num
  refine ⟨U * D * Uᴴ, hD.mul_mul_conjTranspose_same U, ?_, ?_, ?_⟩
  · calc
      _ = U * D * (Uᴴ * U) * D * Uᴴ := by noncomm_ring
      _ = U * (D * D) * Uᴴ := by rw [hU]; noncomm_ring
      _ = U * D * Uᴴ := by rw [hDD]
  · rw [rank_mul_eq_left_of_isUnit_det _ _ hUHd,
      rank_mul_eq_right_of_isUnit_det _ _ hUd, rank_diagonal]
    calc
      Fintype.card {i // d i ≠ 0} = Fintype.card {i : Fin n // e.symm i ≤ j} := by
        apply Fintype.card_congr
        exact Equiv.subtypeEquivRight fun i => by simp [d]
      _ = Fintype.card {i : Fin (Fintype.card (Fin n)) // i ≤ j} :=
        Fintype.card_congr (Equiv.subtypeEquivOfSubtype (p := fun i => i ≤ j) e.symm)
      _ = (Finset.Iic j).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext i
        simp
      _ = j.val + 1 := Fin.card_Iic j
  · have hTD : (diagonal (fun i => (hT.isHermitian.eigenvalues i : ℂ)) - D).PosSemidef := by
      dsimp [D]
      rw [diagonal_sub]
      apply PosSemidef.diagonal
      intro i
      change 0 ≤ (hT.isHermitian.eigenvalues i : ℂ) - d i
      by_cases hi : e.symm i ≤ j
      · have hEig : 1 ≤ hT.isHermitian.eigenvalues i :=
          hj.trans (hT.isHermitian.eigenvalues₀_antitone hi)
        simpa [d, hi] using (show (0 : ℂ) ≤ (hT.isHermitian.eigenvalues i - 1 : ℝ) from
          (RCLike.ofReal_nonneg (K := ℂ)).mpr (sub_nonneg.mpr hEig))
      · simpa [d, hi] using (RCLike.ofReal_nonneg (K := ℂ)).mpr (hT.eigenvalues_nonneg i)
    change (T - U * D * Uᴴ).PosSemidef
    have hspec : T = U * diagonal (fun i => (hT.isHermitian.eigenvalues i : ℂ)) * Uᴴ :=
      hT.isHermitian.spectral_theorem
    rw [hspec]
    convert hTD.mul_mul_conjTranspose_same U using 1 <;> noncomm_ring
end SpectralProjection

section SpectralCount
open _root_.Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Nonnegative inertia can be counted in the descending spectral index. -/
private theorem nonnegIndex_eq_sorted_count {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    nonnegIndex hA =
      (Finset.univ.filter fun i : Fin (Fintype.card n) => 0 ≤ hA.eigenvalues₀ i).card := by
  unfold nonnegIndex
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  let e := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) :
    Fin (Fintype.card n) ≃ n)
  exact Fintype.card_congr (Equiv.subtypeEquiv e.symm (fun _ => Iff.rfl))

/-- The descending value is nonnegative exactly when its full initial segment
fits within the nonnegative inertia count. -/
private theorem eigenvalues_zero_nonneg_iff {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (j : Fin (Fintype.card n)) :
    0 ≤ hA.eigenvalues₀ j ↔ j.val + 1 ≤ nonnegIndex hA := by
  rw [nonnegIndex_eq_sorted_count]
  constructor
  · intro hj
    calc
      j.val + 1 = (Finset.Iic j).card := (Fin.card_Iic j).symm
      _ ≤ (Finset.univ.filter fun i => 0 ≤ hA.eigenvalues₀ i).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_Iic] at hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          hj.trans (hA.eigenvalues₀_antitone hi)⟩
  · intro hc
    by_contra hj
    have hsub : (Finset.univ.filter fun i => 0 ≤ hA.eigenvalues₀ i) ⊆
        Finset.Iio j := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      apply Finset.mem_Iio.mpr
      by_contra hij
      have hle := hA.eigenvalues₀_antitone (le_of_not_gt hij)
      exact hj (hi.trans hle)
    have hh := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hh
    omega

/-- Counting nonnegative eigenvalues after subtraction of the identity supplies
an indexed lower bound for the original Hermitian matrix. -/
theorem one_le_eigenvalue_of_nonnegIndex_sub_one {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (hI : (A - 1).IsHermitian)
    (j : Fin (Fintype.card n)) (hc : j.val + 1 ≤ nonnegIndex hI) :
    1 ≤ hA.eigenvalues₀ j := by
  have hnonneg := (eigenvalues_zero_nonneg_iff hI j).mpr hc
  have hshift : hI.eigenvalues₀ j = hA.eigenvalues₀ j - 1 := by
    have hh := LinGProperty.eigenvalues_zero_add_scalar_finite A hA (-1)
      (by simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul,
        sub_eq_add_neg] using hI) j
    simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul,
      sub_eq_add_neg] using hh
  rw [hshift] at hnonneg
  linarith
end SpectralCount

section OrderedPowers
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {n : ℕ}
local instance : Pow (Matrix (Fin n) (Fin n) ℂ) ℝ := ⟨CFC.rpow⟩

/-- Increasing functions preserve the descending ordering in finite spectral calculus. -/
private theorem eigenvalues_zero_cfc_of_monotone {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ i j, hA.eigenvalues₀ i ≤ hA.eigenvalues₀ j →
      f (hA.eigenvalues₀ i) ≤ f (hA.eigenvalues₀ j))
    (hF : (cfc f A).IsHermitian) (j : Fin (Fintype.card (Fin n))) :
    hF.eigenvalues₀ j = f (hA.eigenvalues₀ j) := by
  have hr : (cfc f A).charpoly.roots.map (RCLike.re : ℂ → ℝ) =
      Finset.univ.val.map (fun i => f (hA.eigenvalues i)) := by
    rw [hA.charpoly_cfc_eq, Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton,
        Multiset.map_map, Function.comp_def, RCLike.ofReal_re]
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _
  have hsort : (Finset.univ.val.map (fun i => f (hA.eigenvalues i))).sort (· ≥ ·) =
      List.ofFn (fun i => f (hA.eigenvalues₀ i)) := by
    change (Multiset.map ((fun i => f (hA.eigenvalues₀ i)) ∘
      (Fintype.equivOfCardEq (Fintype.card_fin _)).symm) Finset.univ.val).sort (· ≥ ·) = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
    simp only [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact (show Antitone (fun i => f (hA.eigenvalues₀ i)) from
      fun _ _ hij => hf _ _ (hA.eigenvalues₀_antitone hij)).sortedGE_ofFn
  have he : hF.eigenvalues₀ = fun i => f (hA.eigenvalues₀ i) := by
    apply List.ofFn_inj.mp
    rw [← hF.sort_roots_charpoly_eq_eigenvalues₀, hr, hsort]
  exact congrFun he j

/-- A nonnegative real power acts componentwise on the descending spectrum. -/
theorem eigenvalues_zero_rpow {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) {r : ℝ} (hr : 0 ≤ r)
    (hR : (CFC.rpow A r).IsHermitian) (j : Fin (Fintype.card (Fin n))) :
    hR.eigenvalues₀ j = (hA.isHermitian.eigenvalues₀ j) ^ r := by
  have he := eigenvalues_zero_cfc_of_monotone hA.isHermitian (fun x => x ^ r)
    (fun i j hij => Real.rpow_le_rpow
      (by simpa only [IsHermitian.eigenvalues, Equiv.symm_apply_apply] using
        hA.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) i)) hij hr)
    (by rw [← CFC.rpow_eq_cfc_real hA.nonneg]; exact hR) j
  simpa only [← CFC.rpow_eq_cfc_real hA.nonneg] using he


end OrderedPowers

section InertiaScaling
open _root_.Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {n : Type} [Fintype n] [DecidableEq n]
theorem eigenvalues_real_smul {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (r : ℝ) (hr : 0 ≤ r) (hB : (r • A).IsHermitian) (i : n) :
    hB.eigenvalues i = r * hA.eigenvalues i := by
  have hs : (r : ℂ) • A = r • A := by
    ext i j
    simp [RCLike.real_smul_eq_coe_mul]
  have hh := LinGProperty.eigenvalues_zero_smul_finite A hA r hr
    (by rw [hs]; exact hB)
    ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
  simpa only [hs, IsHermitian.eigenvalues] using hh

theorem nonnegIndex_real_smul {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (r : ℝ) (hr : 0 < r) (hB : (r • A).IsHermitian) :
    nonnegIndex hB = nonnegIndex hA := by
  unfold nonnegIndex
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    eigenvalues_real_smul hA r hr.le hB i, mul_nonneg_iff_of_pos_left hr]

theorem nonnegIndex_mono {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A ≤ B) :
    nonnegIndex hA ≤ nonnegIndex hB := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans (LinGProperty.eigenvalues_zero_mono_finite hA hB
    (sub_nonneg.mpr hAB).posSemidef
    ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i))

end InertiaScaling

end D5.S3.Quantum.Matrix.SharpWeightedLin
