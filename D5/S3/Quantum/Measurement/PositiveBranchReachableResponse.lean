/- GID: D5/S3/Quantum/Measurement/PositiveBranchReachableResponse
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/PositiveBranchReachableResponse
   mirror-E: none(waiver:finite-dimensional-reachability)
   anchors: []
   utility: none
   digest: Positive Kraus orbits span precisely the original reachable support. -/

import D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit
import D5.S3.Quantum.Measurement.IncoherentCone
import D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Positive weighted orbits and their original Kraus word support. -/

noncomputable section

open Matrix Filter Topology
open D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace

namespace D5.S3.Quantum.Measurement.PositiveBranchReachableResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {n : Type*} {α : Type} [Fintype n] [DecidableEq n] [Fintype α]

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

/-- The trace dual of the weighted continuation map. -/
def weightedDual (K : α → Matrix n n ℂ) (c : α → ℝ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  weightedCP (fun a => (K a)ᴴ) c

/-- Survival effects are defined on the original ambient space; their
quadratic forms on the reachable subspace give the compressed effects. -/
def survivalEffect (K : α → Matrix n n ℂ) (c : α → ℝ) (N : ℕ) : Matrix n n ℂ :=
  (weightedDual K c)^[N] 1

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
  have hmap : Set.MapsTo (weightedCP K c)
      {A : Matrix n n ℂ | A.PosSemidef} {A : Matrix n n ℂ | A.PosSemidef} :=
    fun A hA => weightedCP_psd K c hc hA
  exact Matrix.posSemidef_sum _ fun k _ => hmap.iterate k hρ

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
        u, pow_two, Complex.mul_re, mul_assoc, mul_comm, mul_left_comm]
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
private theorem matrixSupport_eq_range {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    matrixSupport A = LinearMap.range A.toEuclideanLin := by
  rw [matrixSupport, LinearMap.orthogonal_ker,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hA.eq]
private theorem trace_le_of_support_quadratic
    (S : Submodule ℂ (EuclideanSpace ℂ n)) (A σ : Matrix n n ℂ)
    (hσ : σ.PosSemidef) (hsupp : matrixSupport σ ≤ S) (b : ℝ)
    (hbound : ∀ v ∈ S, (inner ℂ v (A.toEuclideanLin v)).re ≤ b * ‖v‖ ^ 2) :
    (σ * A).trace.re ≤ b * σ.trace.re := by
  classical
  let e := hσ.isHermitian.eigenvectorBasis
  let ev := hσ.isHermitian.eigenvalues
  have hev (i : n) : σ.toEuclideanLin (e i) = (ev i : ℂ) • e i := by
    apply WithLp.ofLp_injective 2
    exact hσ.isHermitian.mulVec_eigenvectorBasis i
  have htr : (A * σ).trace = ∑ i, inner ℂ (e i) ((A * σ).toEuclideanLin (e i)) := by
    simpa only [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq] using
      LinearMap.trace_eq_sum_inner (A * σ).toEuclideanLin e
  have hvals : σ.trace.re = ∑ i, ev i := by
    rw [hσ.isHermitian.trace_eq_sum_eigenvalues]
    rw [Complex.re_sum]
    rfl
  rw [Matrix.trace_mul_comm, htr, Complex.re_sum, hvals, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have heq : ((A * σ).toEuclideanLin (e i)) =
      (ev i : ℂ) • A.toEuclideanLin (e i) := by
    change (Matrix.toLpLin 2 2 (A * σ)) (e i) = _
    rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply, hev, map_smul]
  rw [heq, inner_smul_right]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  by_cases hz : ev i = 0
  · simp [hz]
  · have hi : e i ∈ S := hsupp (by
      rw [matrixSupport_eq_range hσ.isHermitian]
      refine ⟨((ev i : ℂ)⁻¹) • e i, ?_⟩
      rw [map_smul, hev, smul_smul,
        inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hz), one_smul])
    have hb := hbound (e i) hi
    rw [e.orthonormal.norm_eq_one, one_pow, mul_one] at hb
    nlinarith [hσ.eigenvalues_nonneg i]
omit [DecidableEq n] in
private theorem weightedCP_trace_pairing (K : α → Matrix n n ℂ) (c : α → ℝ)
    (X Y : Matrix n n ℂ) :
    (weightedCP K c X * Y).trace = (X * weightedDual K c Y).trace := by
  simp only [weightedCP, weightedDual, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.conjTranspose_conjTranspose, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_cycle (K a) X ((K a)ᴴ * Y) |>.trans
      (Matrix.trace_mul_comm ((K a)ᴴ * Y * K a) X)
omit [DecidableEq n] in
private theorem weightedCP_iterate_trace (K : α → Matrix n n ℂ) (c : α → ℝ)
    (N : ℕ) (X Y : Matrix n n ℂ) :
    ((weightedCP K c)^[N] X * Y).trace =
      (X * (weightedDual K c)^[N] Y).trace := by
  induction N generalizing X Y with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', weightedCP_trace_pairing, ih,
      Function.iterate_succ_apply]
private theorem weighted_survival_limit {d : ℕ}
    (K : α → Matrix (Fin d) (Fin d) ℂ) (c : α → ℝ) (hc : ∀ a, 0 < c a)
    (hcomp : weightedDual K c 1 ≤ 1) :
    ∃ F : Matrix (Fin d) (Fin d) ℂ,
      Tendsto (survivalEffect K c) atTop (𝓝 F) ∧ 0 ≤ F ∧
      weightedDual K c F = F ∧
      ∀ X : Matrix (Fin d) (Fin d) ℂ,
        Tendsto (fun N => ((weightedCP K c)^[N] X).trace) atTop (𝓝 (X * F).trace) := by
  classical
  let Q : α → Matrix (Fin d) (Fin d) ℂ := fun a => (Real.sqrt (c a) : ℂ) • K a
  have hQ (X : Matrix (Fin d) (Fin d) ℂ) :
      D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.noClickDual Q X =
        weightedDual K c X := by
    simp only [D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.noClickDual,
      weightedDual, weightedCP, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.conjTranspose_conjTranspose]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Q, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Complex.star_def, Complex.conj_ofReal,
      ← Complex.ofReal_mul, Real.mul_self_sqrt (hc a).le]
  obtain ⟨A, hA⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hcomp)
  have hA' : 1 - weightedDual K c 1 = Aᴴ * A := hA
  have hcomplete : (∑ a, (Q a)ᴴ * Q a) + ∑ _ : Unit, Aᴴ * A = 1 := by
    have hsum : (∑ a, (Q a)ᴴ * Q a) = weightedDual K c 1 := by
      simpa only [D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.noClickDual,
        Matrix.mul_one] using hQ 1
    rw [hsum, Fintype.sum_unique, ← hA']
    abel
  obtain ⟨F, hlim, _, hF, _, hfix, _, htrace⟩ :=
    survival_tendsto_maximal_fixed_effect Q (fun _ : Unit => A) hcomplete
  have hsurv (N : ℕ) :
      D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.survival Q N =
        survivalEffect K c N := by
    have hstep : Function.Semiconj
        (D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.survival Q)
        Nat.succ (weightedDual K c) := fun j => hQ _
    simpa only [Nat.succ_iterate, Nat.zero_add,
      D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.survival,
      survivalEffect] using hstep.iterate_right N 0
  have hsurvfun :
      D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.survival Q =
        survivalEffect K c := funext hsurv
  rw [hsurvfun] at hlim
  refine ⟨F, hlim, hF, ?_, ?_⟩
  · simpa only [hQ] using hfix
  · intro X
    have hpair (N : ℕ) : ((weightedCP K c)^[N] X).trace =
        (X * D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.survival Q N).trace := by
      rw [hsurv, survivalEffect, ← weightedCP_iterate_trace, Matrix.mul_one]
    simpa only [← hpair] using htrace X
/-- Termination from the single original state gives a common finite return
gap for every direction in its original Kraus reachable space. The inequality
is exactly `I_S - (T*)^N(I_S) ≥ I_S / 2`, written as quadratic forms. -/
private theorem initial_gap_quadratic {d : ℕ}
    (K : α → Matrix (Fin d) (Fin d) ℂ) (c : α → ℝ) (hc : ∀ a, 0 < c a)
    (hcomp : weightedDual K c 1 ≤ 1) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef)
    (hterm : Tendsto (fun N => ((weightedCP K c)^[N] ρ).trace) atTop (𝓝 0)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ v ∈ reachableSpace K ρ,
      (inner ℂ v ((survivalEffect K c N).toEuclideanLin v)).re ≤ ‖v‖ ^ 2 / 2 := by
  obtain ⟨L, μ, hμ, hsupp, _⟩ := finite_reachable_faithful_sum K c hc ρ hρ
  obtain ⟨F, hlim, hF, hfix, htrace⟩ := weighted_survival_limit K c hc hcomp
  have hρF : (ρ * F).trace = 0 := tendsto_nhds_unique (htrace ρ) hterm
  have hFiter (k : ℕ) : (weightedDual K c)^[k] F = F :=
    Function.IsFixedPt.iterate hfix k
  have hRF : (F * orbitSum K c ρ L).trace = 0 := by
    rw [Matrix.trace_mul_comm]
    simp only [orbitSum, Matrix.sum_mul, Matrix.trace_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [weightedCP_iterate_trace, hFiter, hρF]
  have hrange :=
    D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity.zero_trace_support
      F (orbitSum K c ρ L) (Matrix.nonneg_iff_posSemidef.mp hF)
      (orbitSum_psd K c (fun a => (hc a).le) hρ L) hRF
  have hkill : ∀ v ∈ reachableSpace K ρ, F.toEuclideanLin v = 0 := by
    intro v hv
    have hv' : v ∈ LinearMap.range (orbitSum K c ρ L).toEuclideanLin := by
      rw [← matrixSupport_eq_range (orbitSum_psd K c (fun a => (hc a).le) hρ L).isHermitian,
        hsupp]
      exact hv
    exact hrange hv'
  let e : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :=
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).toAlgEquiv.toLinearMap
  have he : Continuous e := e.continuous_of_finiteDimensional
  have hn : Tendsto (fun N => ‖e (survivalEffect K c N) - e F‖) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self, norm_zero] using
      (((he.tendsto F).comp hlim).sub_const (e F)).norm
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro v hv
  have hn' : ‖e (survivalEffect K c (max N 1)) - e F‖ < 1 / 2 :=
    hN (max N 1) (le_max_left _ _)
  have hq : (inner ℂ v ((survivalEffect K c (max N 1)).toEuclideanLin v)).re =
      (inner ℂ v ((e (survivalEffect K c (max N 1)) - e F) v)).re := by
    simp only [_root_.sub_apply, e]
    change (inner ℂ v ((survivalEffect K c (max N 1)).toEuclideanLin v)).re =
      (inner ℂ v ((survivalEffect K c (max N 1)).toEuclideanLin v -
        F.toEuclideanLin v)).re
    rw [hkill v hv, sub_zero]
  rw [hq]
  calc
    _ ≤ ‖v‖ * ‖(e (survivalEffect K c (max N 1)) - e F) v‖ :=
      re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖v‖ * (‖e (survivalEffect K c (max N 1)) - e F‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ‖v‖ ^ 2 / 2 := by nlinarith [norm_nonneg v]
/-- The same finite block controls both pure directions and every positive
state supported on the original reachable space, without renormalizing the state. -/
theorem initial_termination_uniform_reachable_gap {d : ℕ}
    (K : α → Matrix (Fin d) (Fin d) ℂ) (c : α → ℝ) (hc : ∀ a, 0 < c a)
    (hcomp : weightedDual K c 1 ≤ 1) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef)
    (hterm : Tendsto (fun N => ((weightedCP K c)^[N] ρ).trace) atTop (𝓝 0)) :
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ v ∈ reachableSpace K ρ,
        (inner ℂ v ((survivalEffect K c N).toEuclideanLin v)).re ≤ ‖v‖ ^ 2 / 2) ∧
      ∀ σ : Matrix (Fin d) (Fin d) ℂ, σ.PosSemidef →
        matrixSupport σ ≤ reachableSpace K ρ →
        ((weightedCP K c)^[N] σ).trace.re ≤ σ.trace.re / 2 := by
  obtain ⟨N, hN, hgap⟩ := initial_gap_quadratic K c hc hcomp ρ hρ hterm
  refine ⟨N, hN, hgap, ?_⟩
  intro σ hσ hsupp
  have h := trace_le_of_support_quadratic (reachableSpace K ρ)
    (survivalEffect K c N) σ hσ hsupp (1 / 2) (by
      intro v hv
      simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hgap v hv)
  rw [← Matrix.mul_one ((weightedCP K c)^[N] σ), weightedCP_iterate_trace]
  simpa only [survivalEffect, div_eq_mul_inv, mul_comm, one_mul] using h
omit [Fintype α] in
private theorem reachable_kraus_invariant (K : α → Matrix n n ℂ)
    (ρ : Matrix n n ℂ) (a : α) :
    ∀ v ∈ reachableSpace K ρ, (K a).toEuclideanLin v ∈ reachableSpace K ρ := by
  have hle : reachableSpace K ρ ≤
      (reachableSpace K ρ).comap (K a).toEuclideanLin := by
    change (⨆ l, wordSpan K ρ l) ≤ _
    apply iSup_le
    intro l
    apply Submodule.span_le.mpr
    rintro y ⟨w, hw, v, hv, rfl⟩
    change (K a).toEuclideanLin ((krausWord K w).toEuclideanLin v) ∈ reachableSpace K ρ
    apply (le_iSup (fun m => wordSpan K ρ m) (l + 1))
    apply Submodule.subset_span
    refine ⟨a :: w, by simpa using Nat.succ_le_succ hw, v, hv, ?_⟩
    simp only [krausWord, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
      LinearMap.comp_apply]
  exact fun v hv => hle hv
private theorem weightedCP_reachable_support (K : α → Matrix n n ℂ)
    (c : α → ℝ) (hc : ∀ a, 0 ≤ c a) (ρ σ : Matrix n n ℂ)
    (hσ : σ.PosSemidef) (hs : matrixSupport σ ≤ reachableSpace K ρ) :
    matrixSupport (weightedCP K c σ) ≤ reachableSpace K ρ := by
  rw [matrixSupport_eq_range (weightedCP_psd K c hc hσ).isHermitian]
  rintro y ⟨v, rfl⟩
  simp only [weightedCP, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.smul_mem
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  change (K a).toEuclideanLin (σ.toEuclideanLin ((K a)ᴴ.toEuclideanLin v)) ∈ reachableSpace K ρ
  apply reachable_kraus_invariant K ρ a
  apply hs
  rw [matrixSupport_eq_range hσ.isHermitian]
  exact ⟨(K a)ᴴ.toEuclideanLin v, rfl⟩
omit [DecidableEq n] in
private theorem weightedCP_mono (K : α → Matrix n n ℂ)
    (c : α → ℝ) (hc : ∀ a, 0 ≤ c a) :
    Monotone (weightedCP K c) := by
  exact (monotone_iff_map_nonneg (weightedCP K c)).mpr fun X hX =>
    Matrix.nonneg_iff_posSemidef.mpr
      (weightedCP_psd K c hc (Matrix.nonneg_iff_posSemidef.mp hX))
omit [DecidableEq n] in
private theorem weightedCP_weight_mono (K : α → Matrix n n ℂ)
    (c b : α → ℝ) (hcb : ∀ a, b a ≤ c a)
    (X : Matrix n n ℂ) (hX : 0 ≤ X) :
    weightedCP K b X ≤ weightedCP K c X := by
  rw [Matrix.le_iff]
  have hd : weightedCP K c X - weightedCP K b X =
      weightedCP K (fun a => c a - b a) X := by
    simp only [weightedCP, LinearMap.coe_mk, AddHom.coe_mk,
      Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib]
  rw [hd]
  exact weightedCP_psd K _ (fun a => sub_nonneg.mpr (hcb a))
    (Matrix.nonneg_iff_posSemidef.mp hX)
omit [DecidableEq n] in
private theorem weightedCP_scale (K : α → Matrix n n ℂ)
    (c : α → ℝ) (g : ℝ) (X : Matrix n n ℂ) :
    weightedCP K (fun a => g * c a) X = (g : ℂ) • weightedCP K c X := by
  simp only [weightedCP, LinearMap.coe_mk, AddHom.coe_mk,
    Complex.ofReal_mul, mul_smul, Finset.smul_sum]
omit [DecidableEq n] in
private theorem positive_iterate (K : α → Matrix n n ℂ)
    (c : α → ℝ) (hc : ∀ a, 0 ≤ c a) (X : Matrix n n ℂ)
    (hX : 0 ≤ X) (k : ℕ) : 0 ≤ (weightedCP K c)^[k] X := by
  have hmap : Set.MapsTo (weightedCP K c)
      {A : Matrix n n ℂ | 0 ≤ A} {A : Matrix n n ℂ | 0 ≤ A} :=
    fun A hA => Matrix.nonneg_iff_posSemidef.mpr
      (weightedCP_psd K c hc (Matrix.nonneg_iff_posSemidef.mp hA))
  exact hmap.iterate k hX

private theorem return_telescoping (K : α → Matrix n n ℂ)
    (c : α → ℝ) (N : ℕ) :
    1 - survivalEffect K c N =
      ∑ k ∈ Finset.range N, (weightedDual K c)^[k] (1 - weightedDual K c 1) := by
  have h := congrArg (fun T : Module.End ℂ (Matrix n n ℂ) => T 1)
    (geom_sum_mul_neg (weightedDual K c) N)
  simpa only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply, Module.End.pow_apply, survivalEffect] using h.symm

private theorem return_comparison (K : α → Matrix n n ℂ)
    (c b : α → ℝ) (hc : ∀ a, 0 ≤ c a) (hb : ∀ a, 0 ≤ b a)
    (g : ℝ) (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hcb : ∀ a, g * b a ≤ c a)
    (hF : 0 ≤ 1 - weightedDual K b 1)
    (hcompare : (g : ℂ) • (1 - weightedDual K b 1) ≤ 1 - weightedDual K c 1)
    (N : ℕ) :
    ((g ^ N : ℝ) : ℂ) • (1 - survivalEffect K b N) ≤ 1 - survivalEffect K c N := by
  have hp k : 0 ≤ (weightedDual K b)^[k] (1 - weightedDual K b 1) :=
    positive_iterate (fun a => (K a)ᴴ) b hb _ hF k
  have hm := weightedCP_mono (fun a => (K a)ᴴ) c hc
  have hi k : ((g ^ (k + 1) : ℝ) : ℂ) •
      (weightedDual K b)^[k] (1 - weightedDual K b 1) ≤
        (weightedDual K c)^[k] (1 - weightedDual K c 1) := by
    apply hm.seq_le_seq (x := fun j => ((g ^ (j + 1) : ℝ) : ℂ) •
      (weightedDual K b)^[j] (1 - weightedDual K b 1))
      (y := fun j => (weightedDual K c)^[j] (1 - weightedDual K c 1)) k
    · simpa using hcompare
    · intro j _
      rw [Function.iterate_succ_apply', map_smul]
      have hw := weightedCP_weight_mono (fun a => (K a)ᴴ) c
        (fun a => g * b a) hcb _ (hp j)
      rw [weightedCP_scale] at hw
      have hs := smul_le_smul_of_nonneg_left hw
        (Complex.zero_le_real.mpr (pow_nonneg hg (j + 1)))
      simpa only [pow_succ, Complex.ofReal_mul, mul_smul, weightedDual] using hs
    · intro j _
      rw [Function.iterate_succ_apply']
      exact le_rfl
  rw [return_telescoping, return_telescoping, Finset.smul_sum]
  apply Finset.sum_le_sum
  intro k hk
  exact (smul_le_smul_of_nonneg_right
    (Complex.real_le_real.mpr
      (pow_le_pow_of_le_one hg hg1 (by
        exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)))) (hp k)).trans (hi k)
private theorem quadratic_mono {A B : Matrix n n ℂ} (h : A ≤ B)
    (v : EuclideanSpace ℂ n) :
    (inner ℂ v (A.toEuclideanLin v)).re ≤
      (inner ℂ v (B.toEuclideanLin v)).re := by
  have hq := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg (WithLp.ofLp v)
  have hx : 0 ≤ inner ℂ v ((B - A).toEuclideanLin v) := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct_comm] using hq
  have hr := (Complex.nonneg_iff.mp hx).1
  simp only [map_sub, LinearMap.sub_apply, inner_sub_right, Complex.sub_re] at hr
  linarith
private theorem reachable_geometric_tail (K : α → Matrix n n ℂ)
    (c : α → ℝ) (hc : ∀ a, 0 ≤ c a) (hcomp : weightedDual K c 1 ≤ 1)
    (ρ : Matrix n n ℂ) (N : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hgap : ∀ v ∈ reachableSpace K ρ,
      (inner ℂ v ((survivalEffect K c N).toEuclideanLin v)).re ≤ q * ‖v‖ ^ 2)
    (σ : Matrix n n ℂ) (hσ : σ.PosSemidef)
    (hs : matrixSupport σ ≤ reachableSpace K ρ) :
    ∀ k, ((weightedCP K c)^[k] σ).trace.re ≤ q ^ (k / N) * σ.trace.re := by
  have hpos k : ((weightedCP K c)^[k] σ).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (positive_iterate K c hc σ (Matrix.nonneg_iff_posSemidef.mpr hσ) k)
  have hsupp k : matrixSupport ((weightedCP K c)^[k] σ) ≤ reachableSpace K ρ := by
    have hmap : Set.MapsTo (weightedCP K c)
      {X : Matrix n n ℂ | X.PosSemidef ∧ matrixSupport X ≤ reachableSpace K ρ}
      {X : Matrix n n ℂ | X.PosSemidef ∧ matrixSupport X ≤ reachableSpace K ρ} :=
      fun X hX => ⟨weightedCP_psd K c hc hX.1,
        weightedCP_reachable_support K c hc ρ X hX.1 hX.2⟩
    exact (hmap.iterate k ⟨hσ, hs⟩).2
  have hstep (X : Matrix n n ℂ) (hX : X.PosSemidef) :
      (weightedCP K c X).trace.re ≤ X.trace.re := by
    have h := RHLinalg.trace_mul_nonneg_of_posSemidef hX (Matrix.le_iff.mp hcomp)
    change 0 ≤ (X * (1 - weightedDual K c 1)).trace.re at h
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Matrix.mul_one] at h
    have hpair := weightedCP_trace_pairing K c X 1
    rw [Matrix.mul_one] at hpair
    rw [hpair]
    linarith
  have hanti : Antitone (fun k => ((weightedCP K c)^[k] σ).trace.re) := by
    apply antitone_nat_of_succ_le
    intro k
    rw [Function.iterate_succ_apply']
    exact hstep _ (hpos k)
  have hblock (k : ℕ) :
      ((weightedCP K c)^[k * N] σ).trace.re ≤ q ^ k * σ.trace.re := by
    apply (show Monotone (fun r : ℝ => q * r) from
      fun a b hab => mul_le_mul_of_nonneg_left hab hq).seq_le_seq
      (x := fun j => ((weightedCP K c)^[j * N] σ).trace.re)
      (y := fun j => q ^ j * σ.trace.re) k
    · simp
    · intro j _
      rw [Nat.succ_mul, Nat.add_comm, Function.iterate_add_apply]
      have hb := trace_le_of_support_quadratic (reachableSpace K ρ)
        (survivalEffect K c N) _ (hpos (j * N)) (hsupp (j * N)) q hgap
      have hp := weightedCP_iterate_trace K c N ((weightedCP K c)^[j * N] σ) 1
      rw [Matrix.mul_one] at hp
      rw [hp]
      exact hb
    · intro j _
      rw [pow_succ]
      exact le_of_eq (by ring)
  intro k
  exact (hanti (Nat.div_mul_le_self k N)).trans (hblock (k / N))
/-- The minimum of one and all branch-weight ratios on a compact parameter set.
The inserted one also covers an empty branch table. -/
def compactBranchRatio {Θ : Type*} (c : Θ → α → ℝ) (θ₀ : Θ) (C : Set Θ) : ℝ :=
  sInf (insert 1 (⋃ a, (fun θ => c θ a / c θ₀ a) '' C))
private theorem compactBranchRatio_spec {Θ : Type*} [TopologicalSpace Θ]
    (c : Θ → α → ℝ) (U : Set Θ) (θ₀ : Θ) (hθ₀ : θ₀ ∈ U)
    (hpos : ∀ θ ∈ U, ∀ a, 0 < c θ a)
    (hcont : ∀ a, ContinuousOn (fun θ => c θ a) U)
    (C : Set Θ) (hC : IsCompact C) (hCU : C ⊆ U) :
    0 < compactBranchRatio c θ₀ C ∧ compactBranchRatio c θ₀ C ≤ 1 ∧
      ∀ θ ∈ C, ∀ a, compactBranchRatio c θ₀ C * c θ₀ a ≤ c θ a := by
  let A := insert (1 : ℝ) (⋃ a, (fun θ => c θ a / c θ₀ a) '' C)
  have hA : IsCompact A :=
    (isCompact_iUnion (fun a =>
      hC.image_of_continuousOn ((hcont a).mono hCU |>.div_const _))).insert 1
  obtain ⟨x, hx, hxmin⟩ := hA.exists_isLeast (Set.insert_nonempty _ _)
  have hxpos : 0 < x := by
    rcases hx with hx | hx
    · simpa only [hx] using (zero_lt_one : (0 : ℝ) < 1)
    · obtain ⟨a, θ, hθ, rfl⟩ := Set.mem_iUnion.mp hx
      exact div_pos (hpos θ (hCU hθ) a) (hpos θ₀ hθ₀ a)
  have hinf : compactBranchRatio c θ₀ C = x := (show IsLeast A x from ⟨hx, hxmin⟩).csInf_eq
  refine ⟨hinf.symm ▸ hxpos, ?_, ?_⟩
  · rw [hinf]
    exact hxmin (Set.mem_insert _ _)
  · intro θ hθ a
    rw [hinf]
    exact (le_div_iff₀ (hpos θ₀ hθ₀ a)).mp
      (hxmin (Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨a, θ, hθ, rfl⟩)))
omit [DecidableEq n] in
private theorem geometric_trace_tendsto (K : α → Matrix n n ℂ)
    (c : α → ℝ) (hc : ∀ a, 0 ≤ c a) (σ : Matrix n n ℂ)
    (hσ : σ.PosSemidef) (N : ℕ) (hN : 1 ≤ N) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ k, ((weightedCP K c)^[k] σ).trace.re ≤
      q ^ (k / N) * σ.trace.re) :
    Tendsto (fun k => ((weightedCP K c)^[k] σ).trace.re) atTop (𝓝 0) := by
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).comp
    (Nat.tendsto_div_const_atTop (by omega : N ≠ 0))
  apply squeeze_zero (fun k => ?_) hbound
    (by simpa only [zero_mul, Function.comp_apply] using hlim.mul_const σ.trace.re)
  exact (Complex.nonneg_iff.mp
    (Matrix.nonneg_iff_posSemidef.mp
      (positive_iterate K c hc σ (Matrix.nonneg_iff_posSemidef.mpr hσ) k)).trace_nonneg).1
open scoped Matrix.Norms.Elementwise in
private theorem psd_norm_le_trace (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    ‖A‖ ≤ A.trace.re := by
  classical
  have ht := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have hdiag (i : n) : 0 ≤ (A i i).re ∧ (A i i).re ≤ A.trace.re := by
    refine ⟨(Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).1, ?_⟩
    let e := Fintype.equivFin n
    have htr : (A.submatrix e.symm e.symm).trace = A.trace := by
      simpa only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply] using
        e.symm.sum_comp (fun j => A j j)
    have h := D5.S3.Quantum.Measurement.IncoherentCone.psd_diag_le_trace
      (hA.submatrix e.symm) (e i)
    simpa only [RHLinalg.rtrace, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      htr, RCLike.re_eq_complex_re] using h
  have hentry (i j : n) : ‖A i j‖ ≤ A.trace.re := by
    have hb := D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound hA i j
    rw [Complex.normSq_eq_norm_sq] at hb
    nlinarith [mul_le_mul (hdiag i).2 (hdiag j).2 (hdiag j).1 ht,
      norm_nonneg (A i j)]
  exact (pi_norm_le_iff_of_nonneg ht).mpr fun i =>
    (pi_norm_le_iff_of_nonneg ht).mpr fun j => hentry i j
open scoped Matrix.Norms.Elementwise in
private theorem geometric_orbit_summable (K : α → Matrix n n ℂ)
    (c : α → ℝ) (hc : ∀ a, 0 ≤ c a) (σ : Matrix n n ℂ)
    (hσ : σ.PosSemidef) (N : ℕ) (hN : 1 ≤ N) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ k, ((weightedCP K c)^[k] σ).trace.re ≤
      q ^ (k / N) * σ.trace.re) :
    Summable (fun k => (weightedCP K c)^[k] σ) := by
  let : NeZero N := ⟨by omega⟩
  have hp : Summable (fun p : ℕ × Fin N => q ^ p.1) := by
    apply (summable_prod_of_nonneg (fun p => pow_nonneg hq p.1)).mpr
    refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using (summable_geometric_of_lt_one hq hq1).mul_left (N : ℝ)
  have hd : Summable (fun k : ℕ => q ^ (k / N)) :=
    hp.comp_injective (Nat.divModEquiv N).injective
  apply (hd.mul_right σ.trace.re).of_norm_bounded
  intro k
  exact (psd_norm_le_trace _ (Matrix.nonneg_iff_posSemidef.mp
    (positive_iterate K c hc σ (Matrix.nonneg_iff_posSemidef.mpr hσ) k))).trans (hbound k)
private theorem summable_orbit_poisson (K : α → Matrix n n ℂ)
    (c : α → ℝ) (σ : Matrix n n ℂ)
    (hs : Summable (fun k => (weightedCP K c)^[k] σ)) :
    (∑' k, (weightedCP K c)^[k] σ) -
      weightedCP K c (∑' k, (weightedCP K c)^[k] σ) = σ := by
  have hm := (LinearMap.toContinuousLinearMap (weightedCP K c)).map_tsum hs
  change weightedCP K c (∑' k, (weightedCP K c)^[k] σ) =
    ∑' k, weightedCP K c ((weightedCP K c)^[k] σ) at hm
  rw [hm]
  have heq : (fun k => weightedCP K c ((weightedCP K c)^[k] σ)) =
      (fun k => (weightedCP K c)^[k + 1] σ) := by
    funext k
    rw [Function.iterate_succ_apply']
  rw [heq]
  exact sub_eq_iff_eq_add.mpr (by simpa using hs.tsum_eq_zero_add)
private theorem summable_event_response (K : α → Matrix n n ℂ)
    (c : α → ℝ) (hc : ∀ a, 0 ≤ c a) (σ : Matrix n n ℂ)
    (hσ : σ.PosSemidef) (hs : Summable (fun k => (weightedCP K c)^[k] σ))
    (F : Matrix n n ℂ) (hF : 0 ≤ F) (hFle : F ≤ 1 - weightedDual K c 1) :
    Summable (fun k => (F * (weightedCP K c)^[k] σ).trace) ∧
      (∑' k, (F * (weightedCP K c)^[k] σ).trace) =
        (F * ∑' k, (weightedCP K c)^[k] σ).trace ∧
      0 ≤ (F * ∑' k, (weightedCP K c)^[k] σ).trace.re ∧
      (F * ∑' k, (weightedCP K c)^[k] σ).trace.re ≤ σ.trace.re ∧
      (F = 1 - weightedDual K c 1 → (F * ∑' k, (weightedCP K c)^[k] σ).trace = σ.trace) := by
  let R := ∑' k, (weightedCP K c)^[k] σ
  let f := LinearMap.toContinuousLinearMap
    ((Matrix.traceLinearMap n ℂ ℂ).comp (LinearMap.mulLeft ℂ F))
  have hsum : Summable (fun k => (F * (weightedCP K c)^[k] σ).trace) :=
    f.summable hs
  have heq : (∑' k, (F * (weightedCP K c)^[k] σ).trace) = (F * R).trace :=
    (f.map_tsum hs).symm
  have hR : 0 ≤ R := tsum_nonneg fun k =>
    positive_iterate K c hc σ (Matrix.nonneg_iff_posSemidef.mpr hσ) k
  have hpair := weightedCP_trace_pairing K c R 1
  simp only [Matrix.mul_one] at hpair
  have htotal : ((1 - weightedDual K c 1) * R).trace = σ.trace := by
    rw [Matrix.trace_mul_comm, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub,
      ← hpair, ← Matrix.trace_sub]
    exact congrArg Matrix.trace (summable_orbit_poisson K c σ hs)
  have hlo := RHLinalg.trace_mul_nonneg_of_posSemidef
    (Matrix.nonneg_iff_posSemidef.mp hF) (Matrix.nonneg_iff_posSemidef.mp hR)
  have hhi := RHLinalg.trace_mul_nonneg_of_posSemidef
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hFle))
    (Matrix.nonneg_iff_posSemidef.mp hR)
  change 0 ≤ (((1 - weightedDual K c 1 - F) * R).trace).re at hhi
  rw [Matrix.sub_mul, Matrix.trace_sub, htotal, Complex.sub_re] at hhi
  exact ⟨hsum, heq, hlo, sub_nonneg.mp hhi, fun h => by simpa only [h] using htotal⟩
private theorem summable_on_real_span
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) (s : Set (Matrix n n ℂ))
    (hs : ∀ X ∈ s, Summable (fun k => T^[k] X))
    (X : Matrix n n ℂ) (hX : X ∈ Submodule.span ℝ s) :
    Summable (fun k => T^[k] X) := by
  induction hX using Submodule.span_induction with
  | mem X hX => exact hs X hX
  | zero => simpa only [← Module.End.pow_apply, map_zero] using
      (summable_zero : Summable (fun _ : ℕ => (0 : Matrix n n ℂ)))
  | add X Y _ _ hX hY =>
      simpa only [← Module.End.pow_apply, map_add] using hX.add hY
  | smul r X _ hX =>
      simpa only [← Module.End.pow_apply, map_smul] using hX.const_smul r
/-- A single terminating initial state yields absorption at every internal
parameter and a common geometric tail on each compact parameter set. Both
continuation operators and return effects use the same fixed positive weights.
The block length is independent of the compact set. -/
theorem positive_branch_compact_absorption {d : ℕ} {Θ : Type*} [TopologicalSpace Θ]
    (K : α → Matrix (Fin d) (Fin d) ℂ) (E : α → Matrix (Fin d) (Fin d) ℂ)
    (hE : ∀ a, (E a).PosSemidef) (c : Θ → α → ℝ) (U : Set Θ)
    (hpos : ∀ θ ∈ U, ∀ a, 0 < c θ a)
    (hcont : ∀ a, ContinuousOn (fun θ => c θ a) U)
    (hcomplete : ∀ θ ∈ U,
      weightedDual K (c θ) 1 + ∑ a, (c θ a : ℂ) • E a = 1)
    (θ₀ : Θ) (hθ₀ : θ₀ ∈ U) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef)
    (hterm : Tendsto (fun k => ((weightedCP K (c θ₀))^[k] ρ).trace) atTop (𝓝 0)) :
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ θ ∈ U, ∀ σ : Matrix (Fin d) (Fin d) ℂ, σ.PosSemidef →
        matrixSupport σ ≤ reachableSpace K ρ →
        Tendsto (fun k => ((weightedCP K (c θ))^[k] σ).trace.re) atTop (𝓝 0) ∧
          Summable (fun k => (weightedCP K (c θ))^[k] σ) ∧
          (∑' k, (weightedCP K (c θ))^[k] σ) -
            weightedCP K (c θ) (∑' k, (weightedCP K (c θ))^[k] σ) = σ ∧
          ∀ F : Matrix (Fin d) (Fin d) ℂ, 0 ≤ F →
            F ≤ 1 - weightedDual K (c θ) 1 →
            Summable (fun k => (F * (weightedCP K (c θ))^[k] σ).trace) ∧
              (∑' k, (F * (weightedCP K (c θ))^[k] σ).trace) =
                (F * ∑' k, (weightedCP K (c θ))^[k] σ).trace ∧
              0 ≤ (F * ∑' k, (weightedCP K (c θ))^[k] σ).trace.re ∧
              (F * ∑' k, (weightedCP K (c θ))^[k] σ).trace.re ≤ σ.trace.re ∧
              (F = 1 - weightedDual K (c θ) 1 →
                (F * ∑' k, (weightedCP K (c θ))^[k] σ).trace = σ.trace)) ∧
      (∀ θ ∈ U, ∀ X ∈ Submodule.span ℝ
        {σ : Matrix (Fin d) (Fin d) ℂ | σ.PosSemidef ∧
          matrixSupport σ ≤ reachableSpace K ρ},
        Summable (fun k => (weightedCP K (c θ))^[k] X) ∧
          (∑' k, (weightedCP K (c θ))^[k] X) -
            weightedCP K (c θ) (∑' k, (weightedCP K (c θ))^[k] X) = X) ∧
      ∀ C : Set Θ, IsCompact C → C.Nonempty → C ⊆ U →
        let g := compactBranchRatio c θ₀ C
        0 < g ∧ g ≤ 1 ∧
          (∀ θ ∈ C, ∀ σ : Matrix (Fin d) (Fin d) ℂ, σ.PosSemidef →
            matrixSupport σ ≤ reachableSpace K ρ → ∀ k,
            ((weightedCP K (c θ))^[k] σ).trace.re ≤
              (1 - g ^ N / 2) ^ (k / N) * σ.trace.re) ∧
          ∀ σ : Matrix (Fin d) (Fin d) ℂ, σ.PosSemidef →
            matrixSupport σ ≤ reachableSpace K ρ → σ.trace = 1 → ∀ k,
            sSup ((fun θ => ((weightedCP K (c θ))^[k] σ).trace.re) '' C) ≤
              (1 - g ^ N / 2) ^ (k / N) := by
  classical
  have hret (θ : Θ) (hθ : θ ∈ U) :
      1 - weightedDual K (c θ) 1 = ∑ a, (c θ a : ℂ) • E a := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using (hcomplete θ hθ).symm
  have hsub (θ : Θ) (hθ : θ ∈ U) : weightedDual K (c θ) 1 ≤ 1 := by
    apply sub_nonneg.mp
    rw [hret θ hθ]
    exact Finset.sum_nonneg fun a _ => smul_nonneg
      (Complex.zero_le_real.mpr (hpos θ hθ a).le)
      (Matrix.nonneg_iff_posSemidef.mpr (hE a))
  obtain ⟨N, hN, hgap, _⟩ := initial_termination_uniform_reachable_gap
    K (c θ₀) (hpos θ₀ hθ₀) (hsub θ₀ hθ₀) ρ hρ hterm
  have htail (C : Set Θ) (hC : IsCompact C) (hCU : C ⊆ U)
      (θ : Θ) (hθ : θ ∈ C) :
      ∀ σ : Matrix (Fin d) (Fin d) ℂ, σ.PosSemidef →
        matrixSupport σ ≤ reachableSpace K ρ → ∀ k,
        ((weightedCP K (c θ))^[k] σ).trace.re ≤
          (1 - compactBranchRatio c θ₀ C ^ N / 2) ^ (k / N) * σ.trace.re := by
    let g := compactBranchRatio c θ₀ C
    obtain ⟨hg, hg1, hratio⟩ :=
      compactBranchRatio_spec c U θ₀ hθ₀ hpos hcont C hC hCU
    have hF : (g : ℂ) • (1 - weightedDual K (c θ₀) 1) ≤
        1 - weightedDual K (c θ) 1 := by
      rw [hret θ₀ hθ₀, hret θ (hCU hθ), Finset.smul_sum]
      apply Finset.sum_le_sum
      intro a _
      rw [smul_smul, ← Complex.ofReal_mul]
      exact smul_le_smul_of_nonneg_right
        (Complex.real_le_real.mpr (hratio θ hθ a))
        (Matrix.nonneg_iff_posSemidef.mpr (hE a))
    have hcomparison := return_comparison K (c θ) (c θ₀)
      (fun a => (hpos θ (hCU hθ) a).le) (fun a => (hpos θ₀ hθ₀ a).le)
      g hg.le hg1 (hratio θ hθ) (sub_nonneg.mpr (hsub θ₀ hθ₀)) hF N
    have hq : 0 ≤ 1 - g ^ N / 2 := by
      have := pow_le_one₀ hg.le hg1 (n := N)
      linarith
    have hnewgap (v : EuclideanSpace ℂ (Fin d)) (hv : v ∈ reachableSpace K ρ) :
        (inner ℂ v ((survivalEffect K (c θ) N).toEuclideanLin v)).re ≤
          (1 - g ^ N / 2) * ‖v‖ ^ 2 := by
      have hb := quadratic_mono hcomparison v
      have hform (A : Matrix (Fin d) (Fin d) ℂ) :
          (inner ℂ v ((1 - A).toEuclideanLin v)).re =
            ‖v‖ ^ 2 - (inner ℂ v (A.toEuclideanLin v)).re := by
        simp only [map_sub, LinearMap.sub_apply, inner_sub_right, Complex.sub_re,
          Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply]
        change RCLike.re (inner ℂ v v) - _ = _
        rw [inner_self_eq_norm_sq]
      have hscale (t : ℝ) (A : Matrix (Fin d) (Fin d) ℂ) :
          (inner ℂ v (((t : ℂ) • A).toEuclideanLin v)).re =
            t * (inner ℂ v (A.toEuclideanLin v)).re := by
        simp only [map_smul, LinearMap.smul_apply, inner_smul_right,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [hscale, hform, hform] at hb
      have hh := hgap v hv
      nlinarith [pow_nonneg hg.le N]
    exact fun σ hσ hs => reachable_geometric_tail K (c θ)
      (fun a => (hpos θ (hCU hθ) a).le) (hsub θ (hCU hθ))
      ρ N (1 - g ^ N / 2) hq hnewgap σ hσ hs
  have hgeom (θ : Θ) (hθ : θ ∈ U) (σ : Matrix (Fin d) (Fin d) ℂ)
      (hσ : σ.PosSemidef) (hs : matrixSupport σ ≤ reachableSpace K ρ) :
      Tendsto (fun k => ((weightedCP K (c θ))^[k] σ).trace.re) atTop (𝓝 0) ∧
        Summable (fun k => (weightedCP K (c θ))^[k] σ) := by
    have hCU : ({θ} : Set Θ) ⊆ U := Set.singleton_subset_iff.mpr hθ
    obtain ⟨hg, hg1, _⟩ := compactBranchRatio_spec c U θ₀ hθ₀ hpos hcont
      {θ} isCompact_singleton hCU
    have hq : 0 ≤ 1 - compactBranchRatio c θ₀ {θ} ^ N / 2 := by
      have := pow_le_one₀ hg.le hg1 (n := N)
      linarith
    have hq1 : 1 - compactBranchRatio c θ₀ {θ} ^ N / 2 < 1 := by
      have := pow_pos hg N
      linarith
    have hb := htail {θ} isCompact_singleton hCU θ (Set.mem_singleton θ) σ hσ hs
    have hsum := geometric_orbit_summable K (c θ) (fun a => (hpos θ hθ a).le)
      σ hσ N hN _ hq hq1 hb
    exact ⟨geometric_trace_tendsto K (c θ) (fun a => (hpos θ hθ a).le)
      σ hσ N hN _ hq hq1 hb, hsum⟩
  refine ⟨N, hN, ?_, ?_, ?_⟩
  · intro θ hθ σ hσ hs
    obtain ⟨hl, hsum⟩ := hgeom θ hθ σ hσ hs
    exact ⟨hl, hsum, summable_orbit_poisson K (c θ) σ hsum,
      summable_event_response K (c θ) (fun a => (hpos θ hθ a).le) σ hσ hsum⟩
  · intro θ hθ X hX
    have hh := summable_on_real_span ((weightedCP K (c θ)).restrictScalars ℝ)
      {σ : Matrix (Fin d) (Fin d) ℂ | σ.PosSemidef ∧
        matrixSupport σ ≤ reachableSpace K ρ}
      (fun σ hσ => (hgeom θ hθ σ hσ.1 hσ.2).2) X hX
    exact ⟨hh, summable_orbit_poisson K (c θ) X hh⟩
  · intro C hC hCne hCU
    obtain ⟨hg, hg1, _⟩ := compactBranchRatio_spec c U θ₀ hθ₀ hpos hcont C hC hCU
    refine ⟨hg, hg1, htail C hC hCU, ?_⟩
    intro σ hσ hs htr k
    apply csSup_le (hCne.image _)
    rintro x ⟨θ, hθ, rfl⟩
    simpa only [htr, Complex.one_re, mul_one] using htail C hC hCU θ hθ σ hσ hs k
#print axioms positive_branch_compact_absorption
#print axioms finite_orbit_support_eq_word_span
#print axioms finite_reachable_faithful_sum
#print axioms initial_termination_uniform_reachable_gap
end D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
