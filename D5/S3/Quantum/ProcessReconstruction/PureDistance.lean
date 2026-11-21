/- GID: D5/S3/Quantum/ProcessReconstruction/PureDistance
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/PureDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Trace norm from the overlap of two pure unitary channel outputs. -/

import D5.S3.Quantum.ProcessReconstruction.ReconstructionChannels

/-! Trace norm from the overlap of two pure unitary channel outputs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder CStarAlgebra
  Matrix.Norms.L2Operator InnerProductSpace
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance

namespace UnitaryReconstruction

variable {a : Type*} [Fintype a] [DecidableEq a]

local notation "ℓ²" => EuclideanSpace ℂ
local notation "L" => Matrix.toEuclideanCLM (𝕜 := ℂ)

omit [DecidableEq a] in
theorem euclidean_norm_one_of_dot (v : a → ℂ) (hv : star v ⬝ᵥ v = 1) :
    ‖(WithLp.toLp 2 v : ℓ² a)‖ = 1 := by
  let w : ℓ² a := WithLp.toLp 2 v
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  change star v ⬝ᵥ v = (‖w‖ : ℂ) ^ 2 at h
  rw [hv] at h
  have hn : (‖w‖ : ℝ) ^ 2 = 1 := by exact_mod_cast h.symm
  nlinarith [norm_nonneg w]

omit [DecidableEq a] in
theorem dot_one_of_euclidean_norm_one (v : a → ℂ)
    (hv : ‖(WithLp.toLp 2 v : ℓ² a)‖ = 1) : star v ⬝ᵥ v = 1 := by
  let w : ℓ² a := WithLp.toLp 2 v
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  change star v ⬝ᵥ v = (‖w‖ : ℂ) ^ 2 at h
  rw [h, show ‖w‖ = 1 from hv]
  norm_num

theorem unitary_euclidean_norm (U : unitaryGroup a ℂ) (v : ℓ² a) :
    ‖L U.val v‖ = ‖v‖ := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (L U.val v)
  have h' := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h h'
  rw [Matrix.ofLp_toEuclideanCLM, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul] at h
  have hu : U.valᴴ * U.val = 1 := Unitary.star_mul_self_of_mem U.prop
  rw [hu, Matrix.vecMul_one, h'] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by exact_mod_cast h.symm)

set_option linter.unusedDecidableInType false in
theorem traceNorm_outer_le (x y : ℓ² a) :
    traceNorm (vecMulVec (⇑x) (star (⇑y))) ≤ ‖x‖ * ‖y‖ := by
  obtain ⟨S, hS⟩ := (traceNorm_eq_max_re_tr_U (vecMulVec (⇑x) (star (⇑y)))).1
  rw [← hS, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    ← Matrix.ofLp_toEuclideanCLM, ← EuclideanSpace.inner_eq_star_dotProduct]
  exact (Complex.re_le_norm _).trans ((norm_inner_le_norm y (L S.val x)).trans_eq
    (by rw [unitary_euclidean_norm, mul_comm]))

omit [DecidableEq a] in
theorem orthogonal_residual_norm (x y : ℓ² a) (hy : ‖y‖ = 1) :
    ‖x - ⟪y, x⟫_ℂ • y‖ ^ 2 = ‖x‖ ^ 2 - ‖⟪y, x⟫_ℂ‖ ^ 2 := by
  have hp : ⟪y, x - ⟪y, x⟫_ℂ • y⟫_ℂ = 0 := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hy]
    simp
  have ho : ⟪x - ⟪y, x⟫_ℂ • y, ⟪y, x⟫_ℂ • y⟫_ℂ = 0 := by
    have hsymm := inner_conj_symm (𝕜 := ℂ) y (x - ⟪y, x⟫_ℂ • y)
    rw [hp] at hsymm
    have hz : ⟪x - ⟪y, x⟫_ℂ • y, y⟫_ℂ = 0 := by
      simpa only [starRingEnd_apply, star_star, star_zero] using congrArg star hsymm
    rw [inner_smul_right, hz, mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ ho
  rw [sub_add_cancel, norm_smul, hy, mul_one] at h
  linarith

set_option linter.unusedDecidableInType false in
theorem traceNorm_pure_sub_le (x y : ℓ² a) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    traceNorm (vecMulVec (⇑x) (star (⇑x)) - vecMulVec (⇑y) (star (⇑y))) ≤
      2 * Real.sqrt (1 - ‖⟪y, x⟫_ℂ‖ ^ 2) := by
  let v := x - ⟪y, x⟫_ℂ • y
  let w := y - ⟪x, y⟫_ℂ • x
  have hxy : ‖⟪x, y⟫_ℂ‖ = ‖⟪y, x⟫_ℂ‖ := by
    rw [← inner_conj_symm x y, RCLike.norm_conj]
  have hv : ‖v‖ = Real.sqrt (1 - ‖⟪y, x⟫_ℂ‖ ^ 2) := by
    rw [show (1 : ℝ) = ‖x‖ ^ 2 by rw [hx]; norm_num,
      ← orthogonal_residual_norm x y hy, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hw : ‖w‖ = Real.sqrt (1 - ‖⟪y, x⟫_ℂ‖ ^ 2) := by
    rw [← hxy, show (1 : ℝ) = ‖y‖ ^ 2 by rw [hy]; norm_num,
      ← orthogonal_residual_norm y x hx, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hdecomp : vecMulVec (⇑x) (star (⇑x)) - vecMulVec (⇑y) (star (⇑y)) =
      vecMulVec (⇑v) (star (⇑x)) - vecMulVec (⇑y) (star (⇑w)) := by
    ext i j
    simp only [v, w, Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      star_sub, star_mul]
    rw [show star ⟪x, y⟫_ℂ = ⟪y, x⟫_ℂ from inner_conj_symm _ _]
    ring
  rw [hdecomp, sub_eq_add_neg]
  apply (traceNorm_add_le _ _).trans
  rw [traceNorm_neg]
  calc
    _ ≤ ‖v‖ * ‖x‖ + ‖y‖ * ‖w‖ := add_le_add (traceNorm_outer_le v x) (traceNorm_outer_le y w)
    _ = _ := by rw [hv, hw, hx, hy]; ring

set_option maxHeartbeats 1000000 in
-- Expanding the reference-amplified action on rank-one matrices needs a larger budget.
set_option backward.isDefEq.respectTransparency false in
theorem pure_referenceError_le (U V : unitaryGroup a ℂ) {r : Type*}
    [Fintype r] [DecidableEq r] (ρ : DensityState (r × a)) (hPure : IsPure ρ) :
    ∃ v : ℓ² (r × a), ‖v‖ = 1 ∧
      referenceError (conjugation U) (conjugation V) ρ ≤
        2 * Real.sqrt (1 - ‖⟪L (referenceUnitary r V).val v,
          L (referenceUnitary r U).val v⟫_ℂ‖ ^ 2) := by
  obtain ⟨x, hρ⟩ := hPure
  have h : star x ⬝ᵥ x = 1 := by
    have hTrace := ρ.2.2
    rw [hρ] at hTrace
    change (vecMulVec x (star x)).trace = 1 at hTrace
    rwa [Matrix.trace_vecMulVec, dotProduct_comm] at hTrace
  let v : ℓ² (r × a) := WithLp.toLp 2 x
  have hv : ‖v‖ = 1 := euclidean_norm_one_of_dot x h
  refine ⟨v, hv, ?_⟩
  change traceNorm (referenceMatrix (conjugation U) (CStarMatrix.ofMatrix.symm ρ.1) -
    referenceMatrix (conjugation V) (CStarMatrix.ofMatrix.symm ρ.1)) ≤ _
  rw [hρ, Equiv.symm_apply_apply, referenceMatrix_conjugation, referenceMatrix_conjugation]
  simp only [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
  let u := L (referenceUnitary r U).val v
  let w := L (referenceUnitary r V).val v
  have hu : ‖u‖ = 1 := (unitary_euclidean_norm (referenceUnitary r U) v).trans hv
  have hw : ‖w‖ = 1 := (unitary_euclidean_norm (referenceUnitary r V) v).trans hv
  have hux : ⇑u = (referenceUnitary r U).val *ᵥ x := Matrix.ofLp_toEuclideanCLM _ _
  have hwx : ⇑w = (referenceUnitary r V).val *ᵥ x := Matrix.ofLp_toEuclideanCLM _ _
  have hbound := traceNorm_pure_sub_le u w hu hw
  rwa [hux, hwx] at hbound

end UnitaryReconstruction
