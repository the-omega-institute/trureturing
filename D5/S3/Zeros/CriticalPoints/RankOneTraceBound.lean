/- GID: D5/S3/Zeros/CriticalPoints/RankOneTraceBound
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/RankOneTraceBound
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2]
   utility: none
   digest: Unitary rank-one trace bounds and scalar three-lines equality certificates. -/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic

/-! General analytic certificates for unitary traces and strip interpolation. -/

set_option autoImplicit false
noncomputable section

open Set Complex Matrix
open scoped BigOperators ComplexConjugate
namespace D5.S3.Zeros.CriticalPoints.RankOneTraceBound

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem norm_sum_inner_le (r : ι → E) (a : ι → ℝ) (γ : ι → ℂ)
    (ha : ∀ j, 0 ≤ a j) (hγ : ∀ j, ‖γ j‖ = 1) (V : E →ₗᵢ[ℂ] E) :
    ‖∑ j, (a j : ℂ) * γ j * inner ℂ (r j) (V (r j))‖ ≤
      ∑ j, a j * ‖r j‖ ^ 2 := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha j), hγ j,
    mul_one]
  calc
    a j * ‖inner ℂ (r j) (V (r j))‖ ≤ a j * (‖r j‖ * ‖V (r j)‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (ha j)
    _ = a j * ‖r j‖ ^ 2 := by rw [V.norm_map, pow_two]

private theorem phases_eq_of_norm_sum_inner_eq (r : ι → E) (a : ι → ℝ)
    (γ : ι → ℂ) (ha : ∀ j, 0 < a j) (hγ : ∀ j, ‖γ j‖ = 1)
    (V : E →ₗᵢ[ℂ] E) (hr : ∀ i j, inner ℂ (r i) (r j) ≠ 0)
    (heq : ‖∑ j, (a j : ℂ) * γ j * inner ℂ (r j) (V (r j))‖ =
      ∑ j, a j * ‖r j‖ ^ 2) : ∀ i j, γ i = γ j := by
  classical
  let S : ℂ := ∑ j, (a j : ℂ) * γ j * inner ℂ (r j) (V (r j))
  obtain ⟨α, hα, hS⟩ := Complex.exists_norm_eq_mul_self S
  have hαγ (j : ι) : ‖α * γ j‖ = 1 := by rw [norm_mul, hα, hγ, one_mul]
  have hbound (j : ι) :
      ((α * γ j) * inner ℂ (r j) (V (r j))).re ≤ ‖r j‖ ^ 2 := by
    calc
      _ ≤ ‖(α * γ j) * inner ℂ (r j) (V (r j))‖ := Complex.re_le_norm _
      _ = ‖inner ℂ (r j) (V (r j))‖ := by rw [norm_mul, hαγ, one_mul]
      _ ≤ ‖r j‖ * ‖V (r j)‖ := norm_inner_le_norm _ _
      _ = ‖r j‖ ^ 2 := by rw [V.norm_map, pow_two]
  have hsum :
      ∑ j, a j * ((α * γ j) * inner ℂ (r j) (V (r j))).re =
        ∑ j, a j * ‖r j‖ ^ 2 := by
    have hmul : α * S =
        ∑ j, (a j : ℂ) * ((α * γ j) * inner ℂ (r j) (V (r j))) := by
      dsimp [S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hreal := congrArg Complex.re (hS.trans hmul)
    simpa only [Complex.ofReal_re, Complex.re_sum, Complex.re_ofReal_mul] using
      hreal.symm.trans heq
  have hterm (j : ι) :
      ((α * γ j) * inner ℂ (r j) (V (r j))).re = ‖r j‖ ^ 2 := by
    have h := (Finset.sum_eq_sum_iff_of_le
      (fun k (_ : k ∈ (Finset.univ : Finset ι)) =>
        mul_le_mul_of_nonneg_left (hbound k) (ha k).le)).mp hsum j (Finset.mem_univ j)
    exact (mul_left_cancel₀ (ha j).ne' h)
  have hvec (j : ι) : (α * γ j) • V (r j) = r j := by
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℂ)
    · simp only [norm_smul, hαγ, V.norm_map, one_mul, le_refl]
    · rw [← inner_re_symm, inner_smul_right]
      exact hterm j
  intro i j
  have hmul : star (α * γ i) * (α * γ j) = 1 := by
    have h : inner ℂ ((α * γ i) • V (r i)) ((α * γ j) • V (r j)) =
        inner ℂ (r i) (r j) := by rw [hvec i, hvec j]
    simp only [inner_smul_left, inner_smul_right, V.inner_map_map] at h
    apply mul_right_cancel₀ (hr i j)
    simp only [Complex.star_def]
    convert h using 1 <;> ring
  have hself : star (α * γ i) * (α * γ i) = 1 := by
    simpa only [Complex.star_def, hαγ, Complex.ofReal_one, one_pow] using
      Complex.conj_mul' (α * γ i)
  have hα0 : α ≠ 0 := by intro h; simp [h] at hα
  have hstar0 : star (α * γ i) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hself
    exact zero_ne_one hself
  exact mul_left_cancel₀ hα0 (mul_left_cancel₀ hstar0 (hself.trans hmul.symm))

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private noncomputable def unitary_isometry (V : Matrix n n ℂ)
    (hV : V ∈ Matrix.unitaryGroup n ℂ) :
    EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ n :=
  V.toEuclideanLin.isometryOfInner fun x y => by
    exact ContinuousLinearMap.inner_map_map_of_mem_unitary
      (Unitary.map_mem (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) hV) x y

private theorem trace_rank_one_sum (r : ι → EuclideanSpace ℂ n) (a : ι → ℝ)
    (γ : ι → ℂ) (V : Matrix n n ℂ) :
    Matrix.trace (V * ∑ j, ((a j : ℂ) * γ j) •
      Matrix.vecMulVec (r j).ofLp (star (r j).ofLp)) =
        ∑ j, (a j : ℂ) * γ j * inner ℂ (r j) (V.toEuclideanLin (r j)) := by
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, smul_eq_mul,
    EuclideanSpace.inner_eq_star_dotProduct]
  rfl

/-- The unitary trace bound for finite sums of complex rank-one operators. -/
theorem norm_trace_rank_one_sum_le (r : ι → EuclideanSpace ℂ n) (a : ι → ℝ)
    (γ : ι → ℂ) (ha : ∀ j, 0 ≤ a j) (hγ : ∀ j, ‖γ j‖ = 1)
    (V : Matrix n n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ) :
    ‖Matrix.trace (V * ∑ j, ((a j : ℂ) * γ j) •
      Matrix.vecMulVec (r j).ofLp (star (r j).ofLp))‖ ≤
        ∑ j, a j * ‖r j‖ ^ 2 := by
  rw [trace_rank_one_sum]
  exact norm_sum_inner_le r a γ ha hγ (unitary_isometry V hV)

/-- Nonzero pairwise inner products force a common phase whenever the trace bound is sharp. -/
theorem phases_eq_of_norm_trace_rank_one_sum_eq (r : ι → EuclideanSpace ℂ n)
    (a : ι → ℝ) (γ : ι → ℂ) (ha : ∀ j, 0 < a j) (hγ : ∀ j, ‖γ j‖ = 1)
    (V : Matrix n n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ)
    (hr : ∀ i j, inner ℂ (r i) (r j) ≠ 0)
    (heq : ‖Matrix.trace (V * ∑ j, ((a j : ℂ) * γ j) •
      Matrix.vecMulVec (r j).ofLp (star (r j).ofLp))‖ =
        ∑ j, a j * ‖r j‖ ^ 2) : ∀ i j, γ i = γ j := by
  rw [trace_rank_one_sum] at heq
  exact phases_eq_of_norm_sum_inner_eq r a γ ha hγ (unitary_isometry V hV) hr heq

end Matrix

end D5.S3.Zeros.CriticalPoints.RankOneTraceBound

namespace D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment

open Complex.HadamardThreeLines

/-- The normalized three-lines estimate, with equality propagated to the right boundary. -/
theorem strip_moment_bound_and_equality
    {f : ℂ → ℂ} {M : ℝ} (hM : 0 < M)
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (hleft : ∀ z : ℂ, z.re = 0 → ‖f z‖ ≤ 1)
    (hright : ∀ z : ℂ, z.re = 1 → ‖f z‖ ≤ M) :
    (∀ z ∈ verticalClosedStrip 0 1, ‖f z‖ ≤ M ^ z.re) ∧
      (∀ θ : ℝ, 0 < θ → θ < 1 → ‖f (θ : ℂ)‖ = M ^ θ →
        ∀ y : ℝ, ‖f (1 + (y : ℂ) * I)‖ = M) := by
  have hbound : ∀ z ∈ verticalClosedStrip 0 1, ‖f z‖ ≤ M ^ z.re := by
    intro z hz
    simpa using norm_le_interp_of_mem_verticalClosedStrip₀₁' f hz hd hB
      (fun z hz => hleft z hz) (fun z hz => hright z hz)
  refine ⟨hbound, ?_⟩
  intro θ hθ0 hθ1 heq
  let g : ℂ → ℂ := fun z => exp (-(z * (Real.log M : ℂ))) * f z
  have hgnorm (z : ℂ) : ‖g z‖ = ‖f z‖ / M ^ z.re := by
    simp only [g, norm_mul, norm_exp, neg_re, mul_re, ofReal_re, ofReal_im,
      mul_zero, sub_zero, Real.rpow_def_of_pos hM, div_eq_mul_inv,
      ← Real.exp_neg]
    rw [mul_comm]
    congr 2
    ring
  have hgle : ∀ z ∈ verticalClosedStrip 0 1, ‖g z‖ ≤ 1 := by
    intro z hz
    rw [hgnorm]
    exact (div_le_one (Real.rpow_pos_of_pos hM _)).2 (hbound z hz)
  have hgθ : ‖g (θ : ℂ)‖ = 1 := by
    rw [hgnorm, ofReal_re, heq, div_self (ne_of_gt (Real.rpow_pos_of_pos hM _))]
  have hgd : DiffContOnCl ℂ g (verticalStrip 0 1) := by
    have he : Differentiable ℂ (fun z : ℂ => exp (-(z * (Real.log M : ℂ)))) :=
      differentiable_exp.comp ((differentiable_id.mul_const _).neg)
    exact ⟨he.differentiableOn.mul hd.1, he.continuous.continuousOn.mul hd.2⟩
  have hopen : IsOpen (verticalStrip 0 1) := continuous_re.isOpen_preimage _ isOpen_Ioo
  have hconv : Convex ℝ (verticalStrip 0 1) :=
    (convex_halfSpace_re_gt (r := 0)).inter (convex_halfSpace_re_lt (r := 1))
  have hθ : (θ : ℂ) ∈ verticalStrip 0 1 := ⟨hθ0, hθ1⟩
  have hmax : IsMaxOn (norm ∘ g) (verticalStrip 0 1) (θ : ℂ) := by
    intro z hz
    change ‖g z‖ ≤ ‖g (θ : ℂ)‖
    rw [hgθ]
    exact hgle z ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hconstant := Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm
    hconv.isPreconnected hopen hgd hθ hmax
  intro y
  have hy : 1 + (y : ℂ) * I ∈ closure (verticalStrip 0 1) := by
    rw [verticalStrip, closure_preimage_re, closure_Ioo zero_ne_one]
    simp
  have hnorm := congrArg norm (hconstant hy)
  change ‖g (1 + (y : ℂ) * I)‖ = ‖g (θ : ℂ)‖ at hnorm
  rw [hgnorm, hgθ] at hnorm
  simpa using (div_eq_one_iff_eq (ne_of_gt (Real.rpow_pos_of_pos hM _))).1 hnorm

/-- Equality of nonzero rotating phases at every frequency parameter fixes both data. -/
theorem rotating_phase_injective {u v : ℂ} {a b : ℝ} (hu : u ≠ 0)
    (h : ∀ y : ℝ, u * exp ((y : ℂ) * (a : ℂ) * I) =
      v * exp ((y : ℂ) * (b : ℂ) * I)) :
    u = v ∧ a = b := by
  have huv : u = v := by simpa using h 0
  refine ⟨huv, ?_⟩
  have heq : (fun y : ℝ => exp ((y : ℂ) * (a : ℂ) * I)) =
      fun y : ℝ => exp ((y : ℂ) * (b : ℂ) * I) := by
    funext y
    exact mul_left_cancel₀ hu (by simpa only [← huv] using h y)
  have ha : HasDerivAt (fun y : ℝ => exp ((y : ℂ) * (a : ℂ) * I))
      ((a : ℂ) * I) 0 := by
    simpa using ((((hasDerivAt_id (0 : ℂ)).mul_const (a : ℂ)).mul_const I).cexp).comp_ofReal
  have hb : HasDerivAt (fun y : ℝ => exp ((y : ℂ) * (b : ℂ) * I))
      ((b : ℂ) * I) 0 := by
    simpa using ((((hasDerivAt_id (0 : ℂ)).mul_const (b : ℂ)).mul_const I).cexp).comp_ofReal
  rw [heq] at ha
  exact Complex.ofReal_injective (mul_right_cancel₀ I_ne_zero (ha.unique hb))

end D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment
