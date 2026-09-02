/- GID: D5/S3/SpectralTopology/FiniteSpectralLocalizer
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/FiniteSpectralLocalizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite non-Hermitian point gap admits a Hermitian chiral localizer. -/

import D5.S3.Weil.ZetaLinear.Inertia
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Invertible
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Finite spectral localizer

A finite operator `H` is shifted by a complex reference point `z`, while a
Hermitian position observable `X` is shifted by a real reference coordinate
`x`. The spectral localizer combines both shifts into a Hermitian block
matrix. At zero position scale it reduces to the standard chiral
Hermitianization of `H - z I`.

The zero-scale localizer is independent of the position input, squares to the
orthogonal block sum of `(H - z I)(H - z I)ᴴ` and
`(H - z I)ᴴ(H - z I)`, and is negated by conjugation with the involutive
chiral grading. The grading acts involutively on doubled vectors, intertwines
the zero-scale localizer with a sign, and pairs every nonzero eigenvector at
`λ` with a nonzero eigenvector at `-λ`. Hermitian negation exchanges the
strictly positive and strictly negative inertia counts. Chiral conjugation
therefore balances the positive and negative inertia of the zero-scale
localizer, so its finite Hermitian signature vanishes. The finite point-gap
predicate is equivalent to invertibility, nonvanishing determinant, square
invertibility, and invertibility of both Gram blocks of the zero-scale
Hermitianization.

The signature coordinate directly reuses the repository owners
`RHLinalg.posIndex` and `RHLinalg.negIndex`. It is only a finite Hermitian
inertia observable here. Local constancy under norm-controlled perturbations,
index normalization, bulk-boundary correspondence, infinite-volume limits,
and any application to zeta zeros are outside this node.
-/

/- Library-search audit trail (2026-09-02):
   * Repository search found no existing owner named `FiniteSpectralLocalizer`,
     `spectralLocalizer`, `pointGap`, or `localizerSignature`.
   * `HorizonEffectiveIndex` already owns finite singular values, defect
     determinants, strict contraction, and orthogonal block sums. None of
     those objects is redefined here.
   * `RHLinalg.posIndex`, `RHLinalg.negIndex`, the Sylvester subspace
     characterization, and inertia under pull-back already own finite
     Hermitian inertia. The negation and chiral-balance theorems below reuse
     those owners.
   * Pinned Mathlib supplies `Matrix.fromBlocks`,
     `Matrix.IsHermitian.fromBlocks`, `Matrix.fromBlocks_multiply`,
     `Matrix.fromBlocks_toBlocks`, `Matrix.mul_nonsing_inv`,
     `Matrix.isUnit_conjTranspose`, `Matrix.isUnit_iff_isUnit_det`,
     `Matrix.det_mul`, `Matrix.mulVec_mulVec`, `Matrix.mulVec_smul`, and
     `isUnit_pow_iff`.
   * The localizer core below is therefore a new assembly theorem over
     established repository and Mathlib primitives. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Finset Submodule
open scoped Matrix
open scoped ComplexOrder

namespace D5.S3.SpectralTopology.FiniteSpectralLocalizer

open RHLinalg

noncomputable section

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- A Hermitian position observable shifted by a real reference coordinate. -/
def positionShift
    (X : Matrix n n ℂ) (x : ℝ) : Matrix n n ℂ :=
  X - (x : ℂ) • (1 : Matrix n n ℂ)

/-- A possibly non-Hermitian operator shifted by a complex spectral point. -/
def spectralShift
    (H : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  H - z • (1 : Matrix n n ℂ)

/-- The finite Hermitian spectral localizer. -/
def finiteSpectralLocalizer
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks
    ((kappa : ℂ) • positionShift X x)
    (spectralShift H z)
    (spectralShift H z)ᴴ
    (-((kappa : ℂ) • positionShift X x))

/-- The chiral grading on the doubled finite carrier. -/
def chiralGrading : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks
    (1 : Matrix n n ℂ) 0 0 (-1 : Matrix n n ℂ)

/-- A finite point gap at `z` means that `H - z I` is invertible. -/
def HasPointGap (H : Matrix n n ℂ) (z : ℂ) : Prop :=
  IsUnit (spectralShift H z)

/-- The signed Hermitian inertia, using the repository's existing positive and
negative index owners. -/
def hermitianSignature
    {m : Type u} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) : ℤ :=
  (posIndex hA : ℤ) - (negIndex hA : ℤ)

/-- A real shift preserves Hermitianity of the position observable. -/
theorem position_shift_isHermitian
    (X : Matrix n n ℂ) (x : ℝ) (hX : X.IsHermitian) :
    (positionShift X x).IsHermitian := by
  unfold positionShift
  exact hX.sub
    (Matrix.IsHermitian.smul (by simp)
      (by rw [isSelfAdjoint_iff]; simp))

/-- A Hermitian position observable makes the full finite localizer
Hermitian. -/
theorem finite_spectral_localizer_isHermitian
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hX : X.IsHermitian) :
    (finiteSpectralLocalizer X H kappa x z).IsHermitian := by
  have hPosition : (positionShift X x).IsHermitian :=
    position_shift_isHermitian X x hX
  have hDiagonal :
      ((kappa : ℂ) • positionShift X x).IsHermitian := by
    exact hPosition.smul (by rw [isSelfAdjoint_iff]; simp)
  exact hDiagonal.fromBlocks rfl hDiagonal.neg

/-- The finite localizer signature. No perturbation-invariance claim is made in
this definition. -/
def finiteLocalizerSignature
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hX : X.IsHermitian) : ℤ :=
  hermitianSignature
    (finite_spectral_localizer_isHermitian X H kappa x z hX)

/-- At zero position scale the localizer is the chiral Hermitianization of the
spectral shift. -/
theorem finite_spectral_localizer_zero_scale
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ) :
    finiteSpectralLocalizer X H 0 x z =
      Matrix.fromBlocks 0 (spectralShift H z)
        (spectralShift H z)ᴴ 0 := by
  simp [finiteSpectralLocalizer]

/-- At zero scale the localizer is independent of the position matrix and
reference coordinate. -/
theorem finite_spectral_localizer_zero_scale_independent
    (X Y H : Matrix n n ℂ) (x y : ℝ) (z : ℂ) :
    finiteSpectralLocalizer X H 0 x z =
      finiteSpectralLocalizer Y H 0 y z := by
  simp only [finite_spectral_localizer_zero_scale]

/-- The zero-scale localizer is Hermitian without any condition on the
position input. -/
theorem finite_spectral_localizer_zero_scale_isHermitian
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ) :
    (finiteSpectralLocalizer X H 0 x z).IsHermitian := by
  rw [finite_spectral_localizer_zero_scale]
  exact Matrix.isHermitian_zero.fromBlocks rfl Matrix.isHermitian_zero

/-- Squaring the zero-scale localizer produces the two Gram blocks of the
spectral shift. -/
theorem finite_spectral_localizer_zero_scale_sq
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ) :
    finiteSpectralLocalizer X H 0 x z ^ 2 =
      Matrix.fromBlocks
        (spectralShift H z * (spectralShift H z)ᴴ) 0 0
        ((spectralShift H z)ᴴ * spectralShift H z) := by
  rw [pow_two]
  simp only [finite_spectral_localizer_zero_scale]
  rw [Matrix.fromBlocks_multiply]
  simp

/-- The chiral grading is an involution. -/
theorem chiral_grading_sq :
    (chiralGrading : Matrix (n ⊕ n) (n ⊕ n) ℂ) ^ 2 = 1 := by
  rw [pow_two]
  simp [chiralGrading, Matrix.fromBlocks_multiply]

private theorem chiral_grading_isHermitian :
    (chiralGrading : Matrix (n ⊕ n) (n ⊕ n) ℂ).IsHermitian := by
  unfold chiralGrading
  exact Matrix.isHermitian_one.fromBlocks (by simp) Matrix.isHermitian_one.neg

/-- The grading anticommutes with the zero-scale localizer. -/
theorem chiral_anticommutator_zero_scale
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ) :
    chiralGrading * finiteSpectralLocalizer X H 0 x z +
        finiteSpectralLocalizer X H 0 x z * chiralGrading = 0 := by
  ext row column
  rcases row with row | row <;>
    rcases column with column | column <;>
      simp [finite_spectral_localizer_zero_scale, chiralGrading,
        Matrix.fromBlocks_multiply]

/-- Conjugation by the involutive grading negates the zero-scale localizer. -/
theorem chiral_conjugation_zero_scale
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ) :
    chiralGrading * finiteSpectralLocalizer X H 0 x z * chiralGrading =
      -finiteSpectralLocalizer X H 0 x z := by
  ext row column
  rcases row with row | row <;>
    rcases column with column | column <;>
      simp [finite_spectral_localizer_zero_scale, chiralGrading,
        Matrix.fromBlocks_multiply]

/-- Applying the chiral grading twice fixes every doubled vector. -/
theorem chiral_grading_mulVec_involutive
    (v : (n ⊕ n) → ℂ) :
    chiralGrading *ᵥ (chiralGrading *ᵥ v) = v := by
  calc
    chiralGrading *ᵥ (chiralGrading *ᵥ v) =
        (chiralGrading * chiralGrading) *ᵥ v := by
      rw [Matrix.mulVec_mulVec]
    _ = (chiralGrading ^ 2) *ᵥ v := by rw [pow_two]
    _ = v := by rw [chiral_grading_sq, one_mulVec]

/-- The zero-scale localizer intertwines the grading with a sign. -/
theorem chiral_mulVec_intertwining_zero_scale
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ)
    (v : (n ⊕ n) → ℂ) :
    finiteSpectralLocalizer X H 0 x z *ᵥ
        (chiralGrading *ᵥ v) =
      -(chiralGrading *ᵥ
        (finiteSpectralLocalizer X H 0 x z *ᵥ v)) := by
  have hMatrix :
      finiteSpectralLocalizer X H 0 x z * chiralGrading =
        -(chiralGrading * finiteSpectralLocalizer X H 0 x z) := by
    ext row column
    rcases row with row | row <;>
      rcases column with column | column <;>
        simp [finite_spectral_localizer_zero_scale, chiralGrading,
          Matrix.fromBlocks_multiply]
  calc
    finiteSpectralLocalizer X H 0 x z *ᵥ (chiralGrading *ᵥ v) =
        (finiteSpectralLocalizer X H 0 x z * chiralGrading) *ᵥ v := by
      rw [Matrix.mulVec_mulVec]
    _ = (-(chiralGrading * finiteSpectralLocalizer X H 0 x z)) *ᵥ v := by
      rw [hMatrix]
    _ = -((chiralGrading * finiteSpectralLocalizer X H 0 x z) *ᵥ v) := by
      rw [neg_mulVec]
    _ = -(chiralGrading *ᵥ
        (finiteSpectralLocalizer X H 0 x z *ᵥ v)) := by
      rw [Matrix.mulVec_mulVec]

/-- Chiral grading pairs every nonzero zero-scale eigenvector at an eigenvalue
with a nonzero eigenvector at its negative. -/
theorem chiral_eigenpair_pairing_zero_scale
    (X H : Matrix n n ℂ) (x : ℝ) (z eigenvalue : ℂ)
    (v : (n ⊕ n) → ℂ)
    (hv :
      finiteSpectralLocalizer X H 0 x z *ᵥ v =
        eigenvalue • v)
    (hv_ne : v ≠ 0) :
    chiralGrading *ᵥ v ≠ 0 ∧
      finiteSpectralLocalizer X H 0 x z *ᵥ
          (chiralGrading *ᵥ v) =
        (-eigenvalue) • (chiralGrading *ᵥ v) := by
  constructor
  · intro hZero
    apply hv_ne
    have hInvol :=
      chiral_grading_mulVec_involutive (n := n) v
    rw [hZero] at hInvol
    simpa using hInvol.symm
  · calc
      finiteSpectralLocalizer X H 0 x z *ᵥ
          (chiralGrading *ᵥ v) =
          -(chiralGrading *ᵥ
            (finiteSpectralLocalizer X H 0 x z *ᵥ v)) :=
        chiral_mulVec_intertwining_zero_scale X H x z v
      _ = -(chiralGrading *ᵥ (eigenvalue • v)) := by rw [hv]
      _ = -(eigenvalue • (chiralGrading *ᵥ v)) := by
        rw [Matrix.mulVec_smul]
      _ = (-eigenvalue) • (chiralGrading *ᵥ v) := by
        simp

private lemma rank_hermNegPart_eq_negIndex
    {K m : Type*} [RCLike K] [Fintype m] [DecidableEq m]
    {A : Matrix m m K} (hA : A.IsHermitian) :
    (hermNegPart hA).rank = negIndex hA := by
  unfold hermNegPart negIndex
  rw [rank_specMap]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq, negPart_eq_zero, not_le]

open Unitary in
private theorem negDefOn_range_hermNegPart
    {K m : Type*} [RCLike K] [Fintype m] [DecidableEq m]
    {A : Matrix m m K} (hA : A.IsHermitian) :
    PosDefOn (-A) (LinearMap.range (hermNegPart hA).mulVecLin) := by
  rintro _ ⟨y, rfl⟩ hne
  set U : Matrix m m K := ↑hA.eigenvectorUnitary
  set z := (hermNegPart hA).mulVecLin y with hz_def
  change z ≠ 0 at hne
  change 0 < hermForm (-A) z
  set d := star U *ᵥ y with hd_def
  have hc_eq : star U *ᵥ z = fun i => (((hA.eigenvalues i)⁻ : ℝ) : K) * d i := by
    have hz' : z = hermNegPart hA *ᵥ y := rfl
    rw [hz']
    unfold hermNegPart specMap
    rw [conjStarAlgAut_apply, Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc,
      Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, one_mul,
      ← Matrix.mulVec_mulVec, ← hd_def]
    funext i
    simp only [mulVec, diagonal_dotProduct]
  have hformA : hermForm A z =
      ∑ i, hA.eigenvalues i * ((hA.eigenvalues i)⁻) ^ 2 * ‖d i‖ ^ 2 := by
    have hAz : A *ᵥ z = specMap hA id *ᵥ z := by rw [specMap_id]
    unfold hermForm
    rw [hAz, hermForm_specMap hA id z, hc_eq]
    refine sum_congr rfl fun i _ => ?_
    simp only [id_eq, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
    ring
  have hformNegA : hermForm (-A) z =
      ∑ i, (-hA.eigenvalues i) * ((hA.eigenvalues i)⁻) ^ 2 * ‖d i‖ ^ 2 := by
    have hnegform : hermForm (-A) z = -hermForm A z := by
      unfold hermForm
      rw [neg_mulVec, dotProduct_neg, map_neg]
    rw [hnegform, hformA, ← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hformNegA]
  have hterm_nn : ∀ i,
      0 ≤ (-hA.eigenvalues i) * ((hA.eigenvalues i)⁻) ^ 2 * ‖d i‖ ^ 2 := by
    intro i
    rcases le_or_gt 0 (hA.eigenvalues i) with h | h
    · simp [negPart_eq_zero.mpr h]
    · exact mul_nonneg (mul_nonneg (neg_nonneg.mpr h.le) (sq_nonneg _)) (sq_nonneg _)
  refine sum_pos' (fun i _ => hterm_nn i) ?_
  have hUinj : Function.Injective (star U *ᵥ ·) := by
    intro a b hab
    have hab' : star U *ᵥ a = star U *ᵥ b := hab
    have : (U * star U) *ᵥ a = (U * star U) *ᵥ b := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hab']
    rwa [Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2, one_mulVec,
      one_mulVec] at this
  have hc_ne : (fun i => (((hA.eigenvalues i)⁻ : ℝ) : K) * d i) ≠ 0 := by
    rw [← hc_eq]
    intro h
    exact hne (hUinj (h.trans (mulVec_zero _).symm))
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc_ne
  refine ⟨i, mem_univ i, ?_⟩
  simp only [Pi.zero_apply, mul_ne_zero_iff, RCLike.ofReal_ne_zero] at hi
  have hevi : hA.eigenvalues i < 0 := by
    by_contra h
    exact hi.1 (negPart_eq_zero.mpr (not_lt.mp h))
  have hdi : (0 : ℝ) < ‖d i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi.2) 2
  have hnp : (0 : ℝ) < ((hA.eigenvalues i)⁻) ^ 2 := by
    rw [negPart_eq_neg.mpr hevi.le]
    exact pow_pos (neg_pos.mpr hevi) 2
  exact mul_pos (mul_pos (neg_pos.mpr hevi) hnp) hdi

/-- Negating a finite Hermitian matrix exchanges its strictly positive and
strictly negative inertia counts. -/
theorem posIndex_neg_eq_negIndex
    {K m : Type*} [RCLike K] [Fintype m] [DecidableEq m]
    {A : Matrix m m K} (hA : A.IsHermitian) :
    posIndex hA.neg = negIndex hA := by
  apply Nat.le_antisymm
  · obtain ⟨W, hposW, hdimW⟩ :=
      posIndex_eq_max_finrank_posDefOn hA.neg
    rw [← hdimW]
    set L : (m → K) →ₗ[K] (m → K) := (hermNegPart hA).mulVecLin
    have hDecomp : -A = hermNegPart hA - hermPosPart hA := by
      simpa only [neg_sub] using
        (congrArg (fun M : Matrix m m K => -M)
          (hermPosPart_sub_hermNegPart hA)).symm
    have hinj : Function.Injective (L.domRestrict W) := by
      intro left right hEqual
      apply Subtype.ext
      by_contra hCoe
      let difference : W := left - right
      have hDifferenceNe : (difference : m → K) ≠ 0 := by
        intro hZero
        change (left : m → K) - (right : m → K) = 0 at hZero
        exact hCoe (sub_eq_zero.mp hZero)
      have hEqual' : L (left : m → K) = L (right : m → K) := by
        simpa only [LinearMap.domRestrict_apply] using hEqual
      have hDifferenceMap :
          hermNegPart hA *ᵥ (difference : m → K) = 0 := by
        change L ((left : m → K) - (right : m → K)) = 0
        rw [map_sub, hEqual', sub_self]
      have hnegZero :
          hermForm (hermNegPart hA) (difference : m → K) = 0 := by
        unfold hermForm
        rw [hDifferenceMap]
        simp
      have hnonpos :
          hermForm (-A) (difference : m → K) ≤ 0 := by
        rw [hDecomp, hermForm_sub, hnegZero, zero_sub]
        exact neg_nonpos.mpr
          (hermForm_nonneg_of_posSemidef
            (hermPosPart_posSemidef hA) (difference : m → K))
      exact absurd
        (hposW (difference : m → K) difference.property hDifferenceNe)
        (not_lt.mpr hnonpos)
    calc
      Module.finrank K W =
          Module.finrank K (LinearMap.range (L.domRestrict W)) :=
        (LinearMap.finrank_range_of_inj hinj).symm
      _ ≤ Module.finrank K (LinearMap.range L) := by
        apply Submodule.finrank_mono
        rintro y ⟨⟨x, hxW⟩, rfl⟩
        exact ⟨x, rfl⟩
      _ = (hermNegPart hA).rank := rfl
      _ = negIndex hA := rank_hermNegPart_eq_negIndex hA
  · calc
      negIndex hA = (hermNegPart hA).rank :=
        (rank_hermNegPart_eq_negIndex hA).symm
      _ = Module.finrank K
          (LinearMap.range (hermNegPart hA).mulVecLin) := rfl
      _ ≤ posIndex hA.neg :=
        finrank_le_posIndex_of_posDefOn hA.neg
          (negDefOn_range_hermNegPart hA)

private theorem posIndex_eq_negIndex_of_negating_conjugation
    {K m : Type*} [RCLike K] [Fintype m] [DecidableEq m]
    {A grading : Matrix m m K}
    (hA : A.IsHermitian)
    (hGrading : grading.IsHermitian)
    (hConj : grading * A * grading = -A) :
    posIndex hA = negIndex hA := by
  have hForwardRaw := posIndex_conj_le hA grading
  have hForward : posIndex hA.neg ≤ posIndex hA := by
    simpa only [hGrading.eq, hConj] using hForwardRaw
  have hConjNeg : gradingᴴ * (-A) * grading = A := by
    rw [hGrading.eq]
    calc
      grading * (-A) * grading = -(grading * A * grading) := by
        simp
      _ = -(-A) := by rw [hConj]
      _ = A := neg_neg A
  have hReverseRaw := posIndex_conj_le hA.neg grading
  have hReverse : posIndex hA ≤ posIndex hA.neg := by
    simpa only [hConjNeg] using hReverseRaw
  calc
    posIndex hA = posIndex hA.neg := Nat.le_antisymm hReverse hForward
    _ = negIndex hA := posIndex_neg_eq_negIndex hA

/-- Chiral conjugation balances the strictly positive and strictly negative
inertia counts of the zero-scale localizer. -/
theorem zero_scale_localizer_posIndex_eq_negIndex
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ) :
    posIndex (finite_spectral_localizer_zero_scale_isHermitian X H x z) =
      negIndex (finite_spectral_localizer_zero_scale_isHermitian X H x z) := by
  exact posIndex_eq_negIndex_of_negating_conjugation
    (finite_spectral_localizer_zero_scale_isHermitian X H x z)
    (chiral_grading_isHermitian (n := n))
    (chiral_conjugation_zero_scale X H x z)

/-- The finite localizer signature vanishes when the position scale is zero. -/
theorem zero_scale_localizer_signature_eq_zero
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ)
    (hX : X.IsHermitian) :
    finiteLocalizerSignature X H 0 x z hX = 0 := by
  unfold finiteLocalizerSignature hermitianSignature
  have hProof :
      finite_spectral_localizer_isHermitian X H 0 x z hX =
        finite_spectral_localizer_zero_scale_isHermitian X H x z :=
    Subsingleton.elim _ _
  rw [hProof]
  have hBalance :=
    zero_scale_localizer_posIndex_eq_negIndex X H x z
  rw [hBalance]
  simp

/-- Over the complex numbers, the finite point gap is exactly nonvanishing of
the shifted determinant. -/
theorem has_point_gap_iff_det_ne_zero
    (H : Matrix n n ℂ) (z : ℂ) :
    HasPointGap H z ↔ (spectralShift H z).det ≠ 0 := by
  rw [HasPointGap, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- The zero-scale Hermitianization is invertible exactly when the original
shifted operator has a finite point gap. -/
theorem has_point_gap_iff_zero_scale_localizer_isUnit
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ) :
    HasPointGap H z ↔
      IsUnit (finiteSpectralLocalizer X H 0 x z) := by
  constructor
  · intro hGap
    change IsUnit (spectralShift H z) at hGap
    have hGapStar : IsUnit (spectralShift H z)ᴴ :=
      (Matrix.isUnit_conjTranspose (spectralShift H z)).2 hGap
    have hDet : IsUnit (spectralShift H z).det :=
      (Matrix.isUnit_iff_isUnit_det (spectralShift H z)).1 hGap
    have hDetStar : IsUnit ((spectralShift H z)ᴴ).det :=
      (Matrix.isUnit_iff_isUnit_det ((spectralShift H z)ᴴ)).1 hGapStar
    have hRightInverse :
        finiteSpectralLocalizer X H 0 x z *
            Matrix.fromBlocks 0 ((spectralShift H z)ᴴ)⁻¹
              (spectralShift H z)⁻¹ 0 = 1 := by
      rw [finite_spectral_localizer_zero_scale,
        Matrix.fromBlocks_multiply]
      simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
      rw [Matrix.mul_nonsing_inv (spectralShift H z) hDet,
        Matrix.mul_nonsing_inv ((spectralShift H z)ᴴ) hDetStar]
      exact Matrix.fromBlocks_one
    exact
      (Matrix.isUnit_iff_isUnit_det
        (finiteSpectralLocalizer X H 0 x z)).2
          (Matrix.isUnit_det_of_right_inverse hRightInverse)
  · intro hLocalizer
    rcases hLocalizer.exists_right_inv with ⟨inverse, hInverse⟩
    rw [finite_spectral_localizer_zero_scale,
      ← Matrix.fromBlocks_toBlocks inverse,
      Matrix.fromBlocks_multiply] at hInverse
    have hShiftRightInverse :
        spectralShift H z * inverse.toBlocks₂₁ = 1 := by
      simpa only [Matrix.toBlocks_fromBlocks₁₁, Matrix.zero_mul,
        zero_add, ← Matrix.fromBlocks_one] using
          congrArg Matrix.toBlocks₁₁ hInverse
    change IsUnit (spectralShift H z)
    exact
      (Matrix.isUnit_iff_isUnit_det (spectralShift H z)).2
        (Matrix.isUnit_det_of_right_inverse hShiftRightInverse)

/-- A finite point gap is equivalent to nonvanishing of the zero-scale
localizer determinant. -/
theorem has_point_gap_iff_zero_scale_localizer_det_ne_zero
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ) :
    HasPointGap H z ↔
      (finiteSpectralLocalizer X H 0 x z).det ≠ 0 := by
  rw [has_point_gap_iff_zero_scale_localizer_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- A finite point gap is equivalent to invertibility of the square of the
zero-scale localizer. -/
theorem has_point_gap_iff_zero_scale_localizer_sq_isUnit
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ) :
    HasPointGap H z ↔
      IsUnit (finiteSpectralLocalizer X H 0 x z ^ 2) := by
  constructor
  · intro hGap
    have hLocalizer :=
      (has_point_gap_iff_zero_scale_localizer_isUnit X H x z).1 hGap
    exact hLocalizer.pow 2
  · intro hSquare
    have hLocalizer :=
      (isUnit_pow_iff (Nat.succ_ne_zero 1)).1 hSquare
    exact
      (has_point_gap_iff_zero_scale_localizer_isUnit X H x z).2 hLocalizer

/-- A finite point gap is equivalent to invertibility of both Gram blocks of
the spectral shift. -/
theorem has_point_gap_iff_gram_blocks_isUnit
    (H : Matrix n n ℂ) (z : ℂ) :
    HasPointGap H z ↔
      IsUnit (spectralShift H z * (spectralShift H z)ᴴ) ∧
        IsUnit ((spectralShift H z)ᴴ * spectralShift H z) := by
  constructor
  · intro hGap
    change IsUnit (spectralShift H z) at hGap
    have hGapStar : IsUnit (spectralShift H z)ᴴ :=
      (Matrix.isUnit_conjTranspose (spectralShift H z)).2 hGap
    exact ⟨hGap.mul hGapStar, hGapStar.mul hGap⟩
  · rintro ⟨hLeft, _⟩
    apply (has_point_gap_iff_det_ne_zero H z).2
    intro hDet
    have hLeftDetUnit :
        IsUnit (spectralShift H z * (spectralShift H z)ᴴ).det :=
      (Matrix.isUnit_iff_isUnit_det
        (spectralShift H z * (spectralShift H z)ᴴ)).1 hLeft
    have hLeftDetNe :
        (spectralShift H z * (spectralShift H z)ᴴ).det ≠ 0 :=
      isUnit_iff_ne_zero.mp hLeftDetUnit
    apply hLeftDetNe
    rw [Matrix.det_mul, hDet, zero_mul]

/-- Point gaps are preserved by conjugate transpose together with conjugation
of the reference point. -/
theorem has_point_gap_conjTranspose
    (H : Matrix n n ℂ) (z : ℂ) :
    HasPointGap Hᴴ (star z) ↔ HasPointGap H z := by
  have hShift :
      spectralShift Hᴴ (star z) = (spectralShift H z)ᴴ := by
    simp [spectralShift]
  rw [HasPointGap, HasPointGap, hShift, Matrix.isUnit_conjTranspose]

#print axioms position_shift_isHermitian
#print axioms finite_spectral_localizer_isHermitian
#print axioms finite_spectral_localizer_zero_scale
#print axioms finite_spectral_localizer_zero_scale_independent
#print axioms finite_spectral_localizer_zero_scale_isHermitian
#print axioms finite_spectral_localizer_zero_scale_sq
#print axioms chiral_grading_sq
#print axioms chiral_anticommutator_zero_scale
#print axioms chiral_conjugation_zero_scale
#print axioms chiral_grading_mulVec_involutive
#print axioms chiral_mulVec_intertwining_zero_scale
#print axioms chiral_eigenpair_pairing_zero_scale
#print axioms posIndex_neg_eq_negIndex
#print axioms zero_scale_localizer_posIndex_eq_negIndex
#print axioms zero_scale_localizer_signature_eq_zero
#print axioms has_point_gap_iff_det_ne_zero
#print axioms has_point_gap_iff_zero_scale_localizer_isUnit
#print axioms has_point_gap_iff_zero_scale_localizer_det_ne_zero
#print axioms has_point_gap_iff_zero_scale_localizer_sq_isUnit
#print axioms has_point_gap_iff_gram_blocks_isUnit
#print axioms has_point_gap_conjTranspose

end

end D5.S3.SpectralTopology.FiniteSpectralLocalizer