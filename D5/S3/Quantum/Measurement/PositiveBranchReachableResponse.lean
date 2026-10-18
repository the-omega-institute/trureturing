/- GID: D5/S3/Quantum/Measurement/PositiveBranchReachableResponse
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/PositiveBranchReachableResponse
   mirror-E: none(waiver:finite-dimensional-reachability)
   anchors: []
   utility: none
   digest: Positive Kraus orbits span precisely the original reachable support. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Positive weighted orbits and their original Kraus word support. -/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace

namespace D5.S3.Quantum.Measurement.PositiveBranchReachableResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α]

/-- The support of a positive matrix, as the orthogonal complement of its kernel. -/
def matrixSupport (A : Matrix n n ℂ) : Submodule ℂ (EuclideanSpace ℂ n) :=
  (LinearMap.ker A.toEuclideanLin)ᗮ

/-- The same original Kraus family is used for every choice of positive weights. -/
def weightedCP (K : α → Matrix n n ℂ) (c : α → ℝ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := ∑ a, (c a : ℂ) • (K a * X * (K a)ᴴ)
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]
  map_smul' z X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, RingHom.id_apply]
    simp only [Finset.smul_sum, smul_smul]
    congr 1
    ext a
    rw [mul_comm]

/-- Cumulative positive orbit, including its zeroth iterate. -/
def orbitSum (K : α → Matrix n n ℂ) (c : α → ℝ)
    (ρ : Matrix n n ℂ) (l : ℕ) : Matrix n n ℂ :=
  ∑ k ∈ Finset.range (l + 1), (weightedCP K c)^[k] ρ

/-- The empty word is the identity; new letters act on the left. -/
def krausWord (K : α → Matrix n n ℂ) : List α → Matrix n n ℂ
  | [] => 1
  | a :: w => K a * krausWord K w

/-- Span of the images of the original support under words of length at most `l`. -/
def wordSpan (K : α → Matrix n n ℂ) (ρ : Matrix n n ℂ) (l : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ n) :=
  Submodule.span ℂ {y | ∃ w : List α, w.length ≤ l ∧
    ∃ v ∈ matrixSupport ρ, (krausWord K w).toEuclideanLin v = y}

/-- The world independent span of all finite original Kraus words. -/
def reachableSpace (K : α → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    Submodule ℂ (EuclideanSpace ℂ n) :=
  ⨆ l, wordSpan K ρ l

omit [DecidableEq n] in
private theorem weightedCP_psd (K : α → Matrix n n ℂ) (c : α → ℝ)
    (hc : ∀ a, 0 ≤ c a) {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    (weightedCP K c X).PosSemidef := by
  exact Matrix.posSemidef_sum _ fun a _ =>
    (hX.mul_mul_conjTranspose_same (K a)).smul (Complex.zero_le_real.mpr (hc a))

omit [DecidableEq n] in
private theorem weightedCP_quadratic (K : α → Matrix n n ℂ) (c : α → ℝ)
    (X : Matrix n n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ (weightedCP K c X) *ᵥ x =
      ∑ a, (c a : ℂ) *
        (star ((K a)ᴴ *ᵥ x) ⬝ᵥ X *ᵥ ((K a)ᴴ *ᵥ x)) := by
  simp only [weightedCP, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_mulVec,
    dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec]
  have hv : star x ᵥ* K a = star ((K a)ᴴ *ᵥ x) := by
    simpa only [Matrix.conjTranspose_conjTranspose, star_star] using
      Matrix.vecMul_conjTranspose ((K a)ᴴ) (star x)
  rw [hv]

omit [DecidableEq n] in
private theorem weightedCP_kernel (K : α → Matrix n n ℂ) (c : α → ℝ)
    (hc : ∀ a, 0 < c a) {X : Matrix n n ℂ} (hX : X.PosSemidef) (x : n → ℂ) :
    (weightedCP K c X) *ᵥ x = 0 ↔ ∀ a, X *ᵥ ((K a)ᴴ *ᵥ x) = 0 := by
  constructor
  · intro hx
    have hz : (∑ a, (c a : ℂ) *
        (star ((K a)ᴴ *ᵥ x) ⬝ᵥ X *ᵥ ((K a)ᴴ *ᵥ x))) = 0 := by
      rw [← weightedCP_quadratic, hx, dotProduct_zero]
    have each := (Finset.sum_eq_zero_iff_of_nonneg (fun a (_ : a ∈ Finset.univ) =>
      mul_nonneg (Complex.zero_le_real.mpr (hc a).le)
        (hX.dotProduct_mulVec_nonneg ((K a)ᴴ *ᵥ x)))).mp hz
    intro a
    apply hX.dotProduct_mulVec_zero_iff.mp
    exact (mul_eq_zero.mp (each a (Finset.mem_univ a))).resolve_left
      (Complex.ofReal_ne_zero.mpr (hc a).ne')
  · intro hx
    simp only [weightedCP, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_mulVec,
      Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hx,
      Matrix.mulVec_zero, smul_zero, Finset.sum_const_zero]

omit [DecidableEq n] in
private theorem add_psd_kernel {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (x : n → ℂ) :
    (A + B) *ᵥ x = 0 ↔ A *ᵥ x = 0 ∧ B *ᵥ x = 0 := by
  constructor
  · intro hx
    have hz : star x ⬝ᵥ A *ᵥ x + star x ⬝ᵥ B *ᵥ x = 0 := by
      rw [← dotProduct_add, ← Matrix.add_mulVec, hx, dotProduct_zero]
    have h := (add_eq_zero_iff_of_nonneg (hA.dotProduct_mulVec_nonneg x)
      (hB.dotProduct_mulVec_nonneg x)).mp hz
    exact ⟨hA.dotProduct_mulVec_zero_iff.mp h.1, hB.dotProduct_mulVec_zero_iff.mp h.2⟩
  · rintro ⟨hA, hB⟩
    simp [Matrix.add_mulVec, hA, hB]

omit [DecidableEq n] in
private theorem orbitSum_psd (K : α → Matrix n n ℂ) (c : α → ℝ)
    (hc : ∀ a, 0 ≤ c a) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (l : ℕ) :
    (orbitSum K c ρ l).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro k
  induction k with
  | zero => intro _; exact hρ
  | succ k ih =>
    intro hk
    rw [Function.iterate_succ_apply']
    exact weightedCP_psd K c hc (ih (by simp only [Finset.mem_range] at hk ⊢; omega))

omit [DecidableEq n] in
private theorem orbitSum_succ (K : α → Matrix n n ℂ) (c : α → ℝ)
    (ρ : Matrix n n ℂ) (l : ℕ) :
    orbitSum K c ρ (l + 1) = ρ + weightedCP K c (orbitSum K c ρ l) := by
  simp only [orbitSum, map_sum]
  rw [Finset.sum_range_succ']
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  abel

private theorem orbitSum_kernel_words (K : α → Matrix n n ℂ) (c : α → ℝ)
    (hc : ∀ a, 0 < c a) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (l : ℕ)
    (x : n → ℂ) :
    (orbitSum K c ρ l) *ᵥ x = 0 ↔
      ∀ w : List α, w.length ≤ l → ρ *ᵥ ((krausWord K w)ᴴ *ᵥ x) = 0 := by
  induction l generalizing x with
  | zero => simp [orbitSum, krausWord]
  | succ l ih =>
    rw [orbitSum_succ, add_psd_kernel hρ
      (weightedCP_psd K c (fun a => (hc a).le)
        (orbitSum_psd K c (fun a => (hc a).le) hρ l)), weightedCP_kernel K c hc
      (orbitSum_psd K c (fun a => (hc a).le) hρ l)]
    simp only [ih]
    constructor
    · rintro ⟨hzero, hstep⟩ w hw
      cases w with
      | nil => simpa [krausWord] using hzero
      | cons a w =>
        simpa only [krausWord, Matrix.conjTranspose_mul, Matrix.mulVec_mulVec] using
          hstep a w (by simpa using hw)
    · intro h
      refine ⟨by simpa [krausWord] using h [] (by simp), ?_⟩
      intro a w hw
      simpa only [krausWord, Matrix.conjTranspose_mul, Matrix.mulVec_mulVec] using
        h (a :: w) (by simpa using Nat.succ_le_succ hw)

omit [Fintype α] in
private theorem wordSpan_orthogonal (K : α → Matrix n n ℂ) (ρ : Matrix n n ℂ)
    (l : ℕ) (x : EuclideanSpace ℂ n) :
    x ∈ (wordSpan K ρ l)ᗮ ↔ ∀ w : List α, w.length ≤ l →
      ρ.toEuclideanLin ((krausWord K w).toEuclideanLin.adjoint x) = 0 := by
  constructor
  · intro hx w hw
    have hx' : (krausWord K w).toEuclideanLin.adjoint x ∈ (matrixSupport ρ)ᗮ := by
      intro v hv
      rw [LinearMap.adjoint_inner_right]
      exact hx _ (Submodule.subset_span ⟨w, hw, v, hv, rfl⟩)
    simpa only [matrixSupport, Submodule.orthogonal_orthogonal, LinearMap.mem_ker] using hx'
  · intro h
    have hle : wordSpan K ρ l ≤ (ℂ ∙ x)ᗮ := by
      apply Submodule.span_le.mpr
      rintro y ⟨w, hw, v, hv, rfl⟩
      change (krausWord K w).toEuclideanLin v ∈ (ℂ ∙ x)ᗮ
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left,
        ← LinearMap.adjoint_inner_right]
      have hx' : (krausWord K w).toEuclideanLin.adjoint x ∈ (matrixSupport ρ)ᗮ := by
        simpa only [matrixSupport, Submodule.orthogonal_orthogonal, LinearMap.mem_ker]
          using h w hw
      exact hx' v hv
    intro y hy
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hle hy)

/-- Every finite positive orbit sum has exactly the span of the original words
of the same maximum length. The weights do not alter the word family. -/
theorem finite_orbit_support_eq_word_span (K : α → Matrix n n ℂ) (c : α → ℝ)
    (hc : ∀ a, 0 < c a) (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef) (l : ℕ) :
    matrixSupport (orbitSum K c ρ l) = wordSpan K ρ l := by
  have heq : (matrixSupport (orbitSum K c ρ l))ᗮ = (wordSpan K ρ l)ᗮ := by
    ext x
    rw [wordSpan_orthogonal]
    simp only [matrixSupport, Submodule.orthogonal_orthogonal, LinearMap.mem_ker,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.toLp_eq_zero,
      WithLp.ofLp_toLp] using orbitSum_kernel_words K c hc hρ l (WithLp.ofLp x)
  simpa only [Submodule.orthogonal_orthogonal] using congrArg Submodule.orthogonal heq

omit [Fintype α] in
private theorem wordSpan_mono (K : α → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    Monotone (wordSpan K ρ) := by
  intro l m hlm
  apply Submodule.span_mono
  rintro y ⟨w, hw, v, hv, rfl⟩
  exact ⟨w, hw.trans hlm, v, hv, rfl⟩

omit [Fintype α] in
private theorem wordSpan_eventually_reachable (K : α → Matrix n n ℂ)
    (ρ : Matrix n n ℂ) : ∃ L, wordSpan K ρ L = reachableSpace K ρ := by
  obtain ⟨L, hL⟩ := (monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian ℂ (EuclideanSpace ℂ n)))
    (⟨wordSpan K ρ, wordSpan_mono K ρ⟩ : ℕ →o Submodule ℂ (EuclideanSpace ℂ n))
  refine ⟨L, le_antisymm (le_iSup (wordSpan K ρ) L) (iSup_le fun l => ?_)⟩
  exact ((wordSpan_mono K ρ) (le_max_right L l)).trans_eq
    (hL (max L l) (le_max_left L l)).symm

private theorem psd_support_quadratic_pos (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (v : EuclideanSpace ℂ n) (hv : v ∈ matrixSupport A) (hv0 : v ≠ 0) :
    0 < (inner ℂ v (A.toEuclideanLin v)).re := by
  have hpos := Matrix.isPositive_toEuclideanLin_iff.mpr hA
  have hne : inner ℂ v (A.toEuclideanLin v) ≠ 0 := by
    intro hz
    have hz' : star (WithLp.ofLp v) ⬝ᵥ A *ᵥ (WithLp.ofLp v) = 0 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct,
        Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct_comm] using hz
    have hker : v ∈ LinearMap.ker A.toEuclideanLin := by
      rw [LinearMap.mem_ker]
      simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.toLp_eq_zero]
        using hA.dotProduct_mulVec_zero_iff.mp hz'
    have hbot : v ∈ (LinearMap.ker A.toEuclideanLin) ⊓
        (LinearMap.ker A.toEuclideanLin)ᗮ := ⟨hker, hv⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hbot
    exact hv0 hbot
  exact (Complex.pos_iff.mp (lt_of_le_of_ne (hpos.inner_nonneg_right v) hne.symm)).1

private theorem psd_support_lower_bound (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ v ∈ matrixSupport A,
      μ * ‖v‖ ^ 2 ≤ (inner ℂ v (A.toEuclideanLin v)).re := by
  let S := matrixSupport A
  let f : S → ℝ := fun v => (inner ℂ (v : EuclideanSpace ℂ n)
    (A.toEuclideanLin v)).re
  have hf : Continuous f := by
    exact Complex.continuous_re.comp (continuous_subtype_val.inner (𝕜 := ℂ)
      (A.toEuclideanLin.continuous_of_finiteDimensional.comp continuous_subtype_val))
  obtain ⟨μ, hμ, hunit⟩ := (isCompact_sphere (0 : S) 1).exists_forall_le'
    hf.continuousOn (a := 0) (by
      intro v hv
      apply psd_support_quadratic_pos A hA v v.property
      have hn : ‖v‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
      intro hz
      have : v = 0 := Subtype.ext hz
      simp [this] at hn)
  refine ⟨μ, hμ, ?_⟩
  intro v hv
  by_cases hv0 : v = 0
  · simp [hv0]
  · let u : S := ⟨v, hv⟩
    have hu0 : u ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
    have hu : ((‖u‖⁻¹ : ℝ) : ℂ) • u ∈ Metric.sphere (0 : S) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu0)]
    have h := hunit _ hu
    have heq : f (((‖u‖⁻¹ : ℝ) : ℂ) • u) =
        ‖v‖⁻¹ ^ 2 * (inner ℂ v (A.toEuclideanLin v)).re := by
      simp [f, map_smul, inner_smul_left, inner_smul_right,
        u, pow_two, Complex.mul_re, mul_assoc]
    rw [heq] at h
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg ‖v‖)
    have hcancel : ‖v‖ ^ 2 * (‖v‖⁻¹ ^ 2 *
        (inner ℂ v (A.toEuclideanLin v)).re) =
        (inner ℂ v (A.toEuclideanLin v)).re := by
      field_simp [hn.ne']
    nlinarith [hcancel]

/-- A finite cumulative orbit is faithful on the original, world independent
reachable space. The zero initial matrix and the zero reachable space are included.
The quadratic inequality is the compressed operator inequality `R ≥ μ I_S`. -/
theorem finite_reachable_faithful_sum (K : α → Matrix n n ℂ) (c : α → ℝ)
    (hc : ∀ a, 0 < c a) (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef) :
    ∃ L : ℕ, ∃ μ : ℝ, 0 < μ ∧
      matrixSupport (orbitSum K c ρ L) = reachableSpace K ρ ∧
      ∀ v ∈ reachableSpace K ρ,
        μ * ‖v‖ ^ 2 ≤ (inner ℂ v ((orbitSum K c ρ L).toEuclideanLin v)).re := by
  obtain ⟨L, hL⟩ := wordSpan_eventually_reachable K ρ
  have hs := (finite_orbit_support_eq_word_span K c hc ρ hρ L).trans hL
  obtain ⟨μ, hμ, hbound⟩ := psd_support_lower_bound (orbitSum K c ρ L)
    (orbitSum_psd K c (fun a => (hc a).le) hρ L)
  exact ⟨L, μ, hμ, hs, fun v hv => hbound v (hs.symm ▸ hv)⟩

#print axioms finite_orbit_support_eq_word_span
#print axioms finite_reachable_faithful_sum

end D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
