/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickCorner
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickCorner
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: Actual positive overlaps reduce to the common interior spectral corner. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickSupport
import D5.S3.Quantum.Divergence.MaximalHockeyStickThreshold

/-! Positive overlap optimization on the actual common spectral corner. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport
open D5.S3.Quantum.Lieb.SupportPerspectiveTransformer
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
open D5.S3.Quantum.Divergence.MaximalHockeyStickSupport
open D5.S3.Quantum.Divergence.MaximalHockeyStickSpectral
open D5.S3.Quantum.Divergence.MaximalHockeyStickThreshold

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickCorner

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Inclusion of a coordinate corner, with its inherited orthonormal basis. -/
def inclusion (p : n → Prop) [DecidablePred p] : Matrix n {i // p i} ℂ :=
  fun i j => if i = j.val then 1 else 0

theorem inclusion_isometry (p : n → Prop) [DecidablePred p] :
    (inclusion p)ᴴ * inclusion p = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, inclusion]
  by_cases hij : i = j
  · subst j; simp
  · have hji : j.val ≠ i.val := fun h => hij (Subtype.ext h.symm)
    simp [Matrix.one_apply, hij, hji]

theorem inclusion_projection (p : n → Prop) [DecidablePred p] :
    inclusion p * (inclusion p)ᴴ = diagonal (fun i => if p i then 1 else 0) := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, inclusion]
  by_cases hi : p i
  · have hsum : (∑ k : {i // p i}, (if i = k.val then (1 : ℂ) else 0) *
        star (if j = k.val then (1 : ℂ) else 0)) =
        star (if j = i then (1 : ℂ) else 0) := by
      rw [Finset.sum_eq_single (⟨i, hi⟩ : {i // p i})]
      · simp
      · intro k _ hk
        have hki : i ≠ k.val := fun h => hk (Subtype.ext h.symm)
        simp [hki]
      · simp
    rw [hsum]
    by_cases hij : i = j
    · subst j; simp [Matrix.diagonal, hi]
    · simp [Matrix.diagonal, hij, Ne.symm hij]
  · have hz : ∀ k : {i // p i}, i ≠ k.val := fun k h => hi (h ▸ k.property)
    simp [hz, Matrix.diagonal, hi]

theorem inclusion_compress (p : n → Prop) [DecidablePred p]
    (X : Matrix n n ℂ) :
    (inclusion p)ᴴ * X * inclusion p = X.submatrix Subtype.val Subtype.val := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, inclusion, Matrix.submatrix]

theorem compress_le (p : n → Prop) [DecidablePred p]
    {X Y : Matrix n n ℂ} (h : X ≤ Y) :
    X.submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val) ≤
      Y.submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val) := by
  apply Matrix.le_iff.mpr
  exact (Matrix.le_iff.mp h).submatrix
    (fun i : {i // p i} => i.val)

theorem extend_le (p : n → Prop) [DecidablePred p]
    {X Y : Matrix {i // p i} {i // p i} ℂ} (h : X ≤ Y) :
    inclusion p * X * (inclusion p)ᴴ ≤ inclusion p * Y * (inclusion p)ᴴ := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub, Matrix.sub_mul] using
    (Matrix.le_iff.mp h).mul_mul_conjTranspose_same (inclusion p)

theorem diagonal_corner_support (d : n → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1) (t : ℝ) (X : Matrix n n ℂ)
    (hX : 0 ≤ X) (hXD : X ≤ diagonal (fun i => (d i : ℂ)))
    (hXB : X ≤ t • (1 - diagonal (fun i => (d i : ℂ)))) :
    let P := diagonal (fun i => if 0 < d i ∧ d i < 1 then (1 : ℂ) else 0)
    P * X = X ∧ X * P = X := by
  classical
  let D := diagonal (fun i => (d i : ℂ))
  let P₀ : Matrix n n ℂ := diagonal (fun i => if d i = 0 then 0 else 1)
  let P₁ : Matrix n n ℂ := diagonal (fun i => if d i = 1 then 0 else 1)
  have hp₀ : P₀.IsHermitian := Matrix.isHermitian_diagonal_iff.mpr (by
    intro i; split_ifs <;> simp)
  have hp₁ : P₁.IsHermitian := Matrix.isHermitian_diagonal_iff.mpr (by
    intro i; split_ifs <;> simp)
  have h₀ : P₀ * D = D := by
    dsimp only [P₀, D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs with hi <;> simp [hi]
  have h₁ : P₁ * (1 - D) = 1 - D := by
    have he : 1 - D = diagonal (fun i => (1 : ℂ) - (d i : ℂ)) := by
      dsimp only [D]
      rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    rw [he]
    dsimp only [P₁]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs with hi <;> simp [hi]
  obtain ⟨h₀X, hX₀⟩ := support_of_nonneg_le_smul D X P₀ hp₀.eq h₀
    hX.posSemidef 1 (by simpa using hXD)
  obtain ⟨h₁X, hX₁⟩ := support_of_nonneg_le_smul (1 - D) X P₁ hp₁.eq h₁
    hX.posSemidef t hXB
  have he : diagonal (fun i => if 0 < d i ∧ d i < 1 then (1 : ℂ) else 0) = P₀ * P₁ := by
    dsimp only [P₀, P₁]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h0 : d i = 0
    · simp [h0]
    by_cases h1 : d i = 1
    · simp [h1]
    have hi : 0 < d i ∧ d i < 1 :=
      ⟨lt_of_le_of_ne (hd i).1 (Ne.symm h0), lt_of_le_of_ne (hd i).2 h1⟩
    simp [h0, h1, hi]
  dsimp only
  rw [he]
  exact ⟨by rw [Matrix.mul_assoc, h₁X, h₀X], by rw [← Matrix.mul_assoc, hX₀, hX₁]⟩

/-- Every actual positive overlap of a positive contraction and its complement
is supported by their common interior spectral projection. -/
theorem overlap_supported (C : Matrix n n ℂ) (hC : C.PosSemidef) (hC1 : C ≤ 1)
    (t : ℝ) (X : Matrix n n ℂ) (hX : X ∈ positiveOverlaps C (t • (1 - C))) :
    interiorProjection C * X = X ∧ X * interiorProjection C = X := by
  classical
  let hH := hC.isHermitian
  let e := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hH.eigenvectorUnitary
  let D := diagonal (fun i => (hH.eigenvalues i : ℂ))
  have hD : e D = C := by
    simpa only [e, D, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      hH.spectral_theorem.symm
  have hP : interiorProjection C =
      e (diagonal (fun i => if 0 < hH.eigenvalues i ∧ hH.eigenvalues i < 1 then 1 else 0)) := by
    have he : interiorProjection C = e (diagonal (fun i =>
        ((if 0 < hH.eigenvalues i ∧ hH.eigenvalues i < 1 then 1 else 0 : ℝ) : ℂ))) := by
      rw [interiorProjection, hH.cfc_eq]
      rfl
    simpa only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using he
  have hbound (i : n) : 0 ≤ hH.eigenvalues i ∧ hH.eigenvalues i ≤ 1 := by
    refine ⟨hC.eigenvalues_nonneg i, ?_⟩
    have hc := map_nonneg e.symm (sub_nonneg.mpr hC1)
    have hd : 0 ≤ 1 - D := by simpa only [map_sub, map_one, ← hD, e.symm_apply_apply] using hc
    have hv := (Complex.nonneg_iff.mp ((Matrix.le_iff.mp hd).diag_nonneg (i := i))).1
    simpa only [sub_zero, Matrix.sub_apply, Matrix.one_apply_eq, D,
      Matrix.diagonal_apply_eq, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Matrix.zero_apply, Complex.zero_re, sub_nonneg] using hv
  have hx0 := map_nonneg e.symm hX.1
  have hxa : e.symm X ≤ e.symm C := by
    have h := map_nonneg e.symm (sub_nonneg.mpr hX.2.1)
    simpa only [map_sub, sub_nonneg] using h
  have hxb : e.symm X ≤ e.symm (t • (1 - C)) := by
    have h := map_nonneg e.symm (sub_nonneg.mpr hX.2.2)
    simpa only [map_sub, sub_nonneg] using h
  rw [← hD, e.symm_apply_apply] at hxa
  have hsm : e.symm (t • (1 - C)) = t • (1 - D) := by
    rw [← Complex.coe_smul t (1 - C), ← Complex.coe_smul t (1 - D),
      map_smul, map_sub, map_one, ← hD, e.symm_apply_apply]
  rw [hsm] at hxb
  obtain ⟨hl, hr⟩ := diagonal_corner_support hH.eigenvalues hbound t (e.symm X) hx0 hxa hxb
  constructor
  · have he := congrArg e hl
    simpa only [map_mul, e.apply_symm_apply, ← hP] using he
  · have he := congrArg e hr
    simpa only [map_mul, e.apply_symm_apply, ← hP] using he

end D5.S3.Quantum.Divergence.MaximalHockeyStickCorner
