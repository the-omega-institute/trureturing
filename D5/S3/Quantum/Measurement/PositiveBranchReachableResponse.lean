/- GID: D5/S3/Quantum/Measurement/PositiveBranchReachableResponse
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/PositiveBranchReachableResponse
   mirror-E: none(waiver:finite-dimensional-reachability)
   anchors: []
   utility: none
   digest: Positive Kraus orbits span precisely the original reachable support. -/

import D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit
import D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
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

private theorem matrixSupport_eq_range {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    matrixSupport A = LinearMap.range A.toEuclideanLin := by
  rw [matrixSupport, LinearMap.orthogonal_ker,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hA.eq]

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
    induction N with
    | zero => rfl
    | succ N ih =>
      rw [D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure.survival, ih,
        hQ]
      simp only [survivalEffect, Function.iterate_succ_apply']
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
theorem initial_termination_uniform_reachable_gap {d : ℕ}
    (K : α → Matrix (Fin d) (Fin d) ℂ) (c : α → ℝ) (hc : ∀ a, 0 < c a)
    (hcomp : weightedDual K c 1 ≤ 1) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef)
    (hterm : Tendsto (fun N => ((weightedCP K c)^[N] ρ).trace) atTop (𝓝 0)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ v ∈ reachableSpace K ρ,
      (inner ℂ v ((survivalEffect K c N).toEuclideanLin v)).re ≤ ‖v‖ ^ 2 / 2 := by
  obtain ⟨L, μ, hμ, hsupp, _⟩ := finite_reachable_faithful_sum K c hc ρ hρ
  obtain ⟨F, hlim, hF, hfix, htrace⟩ := weighted_survival_limit K c hc hcomp
  have hρF : (ρ * F).trace = 0 := tendsto_nhds_unique (htrace ρ) hterm
  have hFiter (k : ℕ) : (weightedDual K c)^[k] F = F := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hfix]
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

#print axioms finite_orbit_support_eq_word_span
#print axioms finite_reachable_faithful_sum
#print axioms initial_termination_uniform_reachable_gap

end D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
