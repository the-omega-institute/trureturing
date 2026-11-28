/- GID: D5/S3/Geometry/Lorentz/AdS4CFT3BulkBoundary4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/AdS4CFT3BulkBoundary4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Anti-de Sitter geometry, real indicial roots and scalar kernels. -/

import OmegaBuild.Commands
import D5.S3.Geometry.Orthogonality.OrthogonalMatrixGenerators
import D5.S3.Analysis.ConformalHalfSpaceKernel
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The ambient quadric, its Poincare chart and scalar fields in four dimensions. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Real Set Filter
open scoped Matrix Topology

namespace D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D

open OmegaMath.OrthogonalMatrixGenerators

abbrev RMat5 := Matrix (Fin 5) (Fin 5) ℝ

def signature23 : Fin 5 → ℝ := ![-1, -1, 1, 1, 1]

def eta23 : RMat5 := metric signature23

def so23Subspace : Submodule ℝ RMat5 := orthogonalSubspace signature23

def so23Generator (a b : Fin 5) : RMat5 := generator signature23 a b

private theorem signature_square (i : Fin 5) : signature23 i * signature23 i = 1 := by
  fin_cases i <;> norm_num [signature23]

theorem so23_isometry_finrank_10 :
    Module.finrank ℝ so23Subspace = 10 ∧
    ∀ a b c d : Fin 5,
      so23Generator a b * so23Generator c d - so23Generator c d * so23Generator a b =
        eta23 b c • so23Generator a d - eta23 a c • so23Generator b d -
          eta23 b d • so23Generator a c + eta23 a d • so23Generator b c := by
  refine ⟨?_, generator_commutator signature23⟩
  change Module.finrank ℝ (orthogonalSubspace signature23) = 10
  rw [(coordinateEquiv signature23 signature_square).finrank_eq,
    Module.finrank_fintype_fun_eq_card]
  decide

def adsForm (X : Fin 5 → ℝ) : ℝ :=
  -X 0 ^ 2 - X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 + X 4 ^ 2

def IsOnAdS4 (L : ℝ) (X : Fin 5 → ℝ) : Prop := adsForm X = -L ^ 2

private theorem adsForm_dot (X : Fin 5 → ℝ) : adsForm X = X ⬝ᵥ (eta23 *ᵥ X) := by
  simp [adsForm, eta23, metric, mulVec_diagonal, dotProduct, Fin.sum_univ_succ, signature23]
  ring

theorem so23_preserves_ads4 (Λ : RMat5) (hΛ : Λᵀ * eta23 * Λ = eta23)
    (X : Fin 5 → ℝ) (L : ℝ) :
    adsForm (Λ *ᵥ X) = adsForm X ∧ (IsOnAdS4 L X → IsOnAdS4 L (Λ *ᵥ X)) := by
  have h : adsForm (Λ *ᵥ X) = adsForm X := by
    rw [adsForm_dot, adsForm_dot]
    calc
      (Λ *ᵥ X) ⬝ᵥ (eta23 *ᵥ (Λ *ᵥ X))
          = X ⬝ᵥ (Λᵀ *ᵥ (eta23 *ᵥ (Λ *ᵥ X))) :=
        (dotProduct_comm _ _).trans
          (dotProduct_transpose_mulVec Λ X (eta23 *ᵥ (Λ *ᵥ X))).symm
      _ = X ⬝ᵥ (eta23 *ᵥ X) := by rw [mulVec_mulVec, mulVec_mulVec, hΛ]
  exact ⟨h, fun hx => h.trans hx⟩

private def patchQuad (z t x y : ℝ) : ℝ := -t ^ 2 + x ^ 2 + y ^ 2 + z ^ 2

def poincareEmbed (L z t x y : ℝ) : Fin 5 → ℝ :=
  ![(L ^ 2 + patchQuad z t x y) / (2 * z), (L / z) * t, (L / z) * x, (L / z) * y,
    (L ^ 2 - patchQuad z t x y) / (2 * z)]

theorem poincareEmbed_on_ads4 {L z : ℝ} (hL : 0 < L) (hz : 0 < z) (t x y : ℝ) :
    IsOnAdS4 L (poincareEmbed L z t x y) ∧
      poincareEmbed L z t x y 0 + poincareEmbed L z t x y 4 = L ^ 2 / z ∧
      0 < L ^ 2 / z := by
  refine ⟨?_, ?_, div_pos (sq_pos_of_pos hL) hz⟩
  · simp [IsOnAdS4, adsForm, poincareEmbed, patchQuad]
    field_simp
    ring
  · simp [poincareEmbed]
    ring

def poincareTangent (L z t x y dz dt dx dy : ℝ) : Fin 5 → ℝ :=
  let q := patchQuad z t x y
  let dq := 2 * (-t * dt + x * dx + y * dy + z * dz)
  ![(dq * z - (L ^ 2 + q) * dz) / (2 * z ^ 2),
    L * (dt * z - t * dz) / z ^ 2, L * (dx * z - x * dz) / z ^ 2,
    L * (dy * z - y * dz) / z ^ 2, (-dq * z - (L ^ 2 - q) * dz) / (2 * z ^ 2)]

theorem poincareEmbed_metric_pullback {z t x y : ℝ → ℝ} {s dz dt dx dy : ℝ}
    (L : ℝ) (hz : 0 < z s) (hdz : HasDerivAt z dz s) (hdt : HasDerivAt t dt s)
    (hdx : HasDerivAt x dx s) (hdy : HasDerivAt y dy s) :
    HasDerivAt (fun u => poincareEmbed L (z u) (t u) (x u) (y u))
      (poincareTangent L (z s) (t s) (x s) (y s) dz dt dx dy) s ∧
    adsForm (poincareTangent L (z s) (t s) (x s) (y s) dz dt dx dy) =
      (L ^ 2 / (z s) ^ 2) * (-dt ^ 2 + dx ^ 2 + dy ^ 2 + dz ^ 2) := by
  have hq : HasDerivAt (fun u => patchQuad (z u) (t u) (x u) (y u))
      (2 * (-t s * dt + x s * dx + y s * dy + z s * dz)) s := by
    convert ((((hdt.pow 2).neg.add (hdx.pow 2)).add (hdy.pow 2)).add (hdz.pow 2)) using 1
    · funext u
      simp [patchQuad, Pi.neg_apply, Pi.add_apply, Pi.pow_apply]
    · simp
      ring
  have hden : HasDerivAt (fun u => 2 * z u) (2 * dz) s := hdz.const_mul 2
  have hn : 2 * z s ≠ 0 := by positivity
  have hleft := (hq.const_add (L ^ 2)).div hden hn
  have hright := ((hasDerivAt_const s (L ^ 2)).sub hq).div hden hn
  have hmiddle (f : ℝ → ℝ) (df : ℝ) (hf : HasDerivAt f df s) :
      HasDerivAt (fun u => L / z u * f u) (L * (df * z s - f s * dz) / (z s)^2) s := by
    convert ((hasDerivAt_const s L).div hdz hz.ne').mul hf using 1
    simp only [Pi.div_apply, zero_mul, zero_sub]
    field_simp
    ring
  constructor
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simp [poincareEmbed, poincareTangent]
      convert hleft using 1 <;> ring
    · simpa [poincareEmbed, poincareTangent] using hmiddle t dt hdt
    · simpa [poincareEmbed, poincareTangent] using hmiddle x dx hdx
    · simpa [poincareEmbed, poincareTangent] using hmiddle y dy hdy
    · simp [poincareEmbed, poincareTangent]
      convert hright using 1 <;> simp [Pi.sub_apply] <;> ring
  · simp [adsForm, poincareTangent, patchQuad]
    field_simp
    ring

def adsConformalFactor (L z : ℝ) : ℝ := z / L

theorem ads4_timelike_conformal_boundary {L : ℝ} (hL : 0 < L) :
    adsConformalFactor L 0 = 0 ∧
    HasDerivAt (adsConformalFactor L) (1 / L) 0 ∧
    1 / L ≠ 0 ∧ (1 / L) ^ 2 = 1 / L ^ 2 ∧ 0 < 1 / L ^ 2 := by
  refine ⟨zero_div _, ?_, one_div_ne_zero hL.ne', ?_, by positivity⟩
  · change HasDerivAt (fun z : ℝ => z / L) (1 / L) 0
    exact (hasDerivAt_id (0 : ℝ)).div_const L
  · rw [div_pow, one_pow]

theorem radial_light_travel {L z₀ : ℝ} (hz₀ : 0 < z₀) :
    0 ∈ Ico 0 z₀ ∧ (∀ τ ∈ Ico 0 z₀,
      0 < z₀ - τ ∧ L ^ 2 / (z₀ - τ) ^ 2 * (-(1 : ℝ) ^ 2 + (-1 : ℝ) ^ 2) = 0) ∧
    IsLeast {τ : ℝ | z₀ - τ = 0} z₀ := by
  refine ⟨⟨le_rfl, hz₀⟩, fun τ hτ => ⟨sub_pos.mpr hτ.2, by ring⟩, sub_self _, ?_⟩
  intro τ hτ
  exact le_of_eq (sub_eq_zero.mp hτ)

theorem radial_proper_distance {L z₀ ε : ℝ} (hz₀ : 0 < z₀) (hε : 0 < ε) :
    (∫ z in ε..z₀, L / z) = L * log (z₀ / ε) := by
  simp_rw [div_eq_mul_inv, intervalIntegral.integral_const_mul]
  rw [integral_inv_of_pos hε hz₀, ← div_eq_mul_inv]

theorem radial_proper_distance_diverges {L z₀ : ℝ} (hL : 0 < L) (hz₀ : 0 < z₀) :
    Tendsto (fun ε => L * log (z₀ / ε)) (𝓝[>] 0) atTop := by
  have h : Tendsto (fun ε => log z₀ - log ε) (𝓝[>] 0) atTop := by
    refine tendsto_atTop.mpr fun a => ?_
    filter_upwards [tendsto_atBot.mp tendsto_log_nhdsGT_zero (log z₀ - a)] with ε hε
    linarith
  apply (Tendsto.const_mul_atTop hL h).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [Real.log_div hz₀.ne' (show 0 < ε from hε).ne']

def ads4MassFromDim (L Δ : ℝ) : ℝ := Δ * (Δ - 3) / L ^ 2

def bfDeltaPlus (μ : ℝ) : ℝ := 3 / 2 + sqrt (9 / 4 + μ)

def bfDeltaMinus (μ : ℝ) : ℝ := 3 / 2 - sqrt (9 / 4 + μ)

theorem bf_bound_real_dimension_iff (μ : ℝ) :
    (∃ Δ : ℝ, Δ * (Δ - 3) = μ) ↔ -(9 / 4 : ℝ) ≤ μ := by
  constructor
  · rintro ⟨Δ, hΔ⟩
    nlinarith [sq_nonneg (Δ - 3 / 2)]
  · intro hμ
    refine ⟨bfDeltaPlus μ, ?_⟩
    unfold bfDeltaPlus
    nlinarith [sq_sqrt (show 0 ≤ 9 / 4 + μ by linarith)]

theorem bf_indicial_roots {μ : ℝ} (hμ : -(9 / 4 : ℝ) ≤ μ) :
    (∀ Δ : ℝ, Δ * (Δ - 3) = μ ↔ Δ = bfDeltaMinus μ ∨ Δ = bfDeltaPlus μ) ∧
      bfDeltaPlus μ + bfDeltaMinus μ = 3 ∧ bfDeltaPlus μ * bfDeltaMinus μ = -μ := by
  have hs : (sqrt (9 / 4 + μ)) ^ 2 = 9 / 4 + μ := sq_sqrt (by linarith)
  have hf (Δ : ℝ) : (Δ - bfDeltaMinus μ) * (Δ - bfDeltaPlus μ) = Δ * (Δ - 3) - μ := by
    unfold bfDeltaMinus bfDeltaPlus
    nlinarith only [hs]
  refine ⟨fun Δ => ?_, ?_, ?_⟩
  · rw [← sub_eq_zero, ← hf, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  · unfold bfDeltaPlus bfDeltaMinus
    ring
  · unfold bfDeltaPlus bfDeltaMinus
    nlinarith only [hs]

theorem bf_root_separation (μ : ℝ) :
    (bfDeltaMinus μ < bfDeltaPlus μ ↔ -(9 / 4 : ℝ) < μ) ∧
      bfDeltaMinus (-(9 / 4)) = 3 / 2 ∧ bfDeltaPlus (-(9 / 4)) = 3 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · have h : bfDeltaMinus μ < bfDeltaPlus μ ↔ 0 < sqrt (9 / 4 + μ) := by
      unfold bfDeltaMinus bfDeltaPlus
      constructor <;> intro ht <;> linarith
    rw [h, sqrt_pos]
    constructor <;> intro ht <;> linarith
  · norm_num [bfDeltaMinus]
  · norm_num [bfDeltaPlus]

theorem bf_unitarity_dual_quantization_window (μ : ℝ) :
    ((∃ Δ : ℝ, Δ * (Δ - 3) = μ) ∧
        1 / 2 ≤ bfDeltaMinus μ ∧ 1 / 2 ≤ bfDeltaPlus μ) ↔
      -(9 / 4 : ℝ) ≤ μ ∧ μ ≤ -(5 / 4 : ℝ) := by
  rw [bf_bound_real_dimension_iff]
  have hplus : 1 / 2 ≤ bfDeltaPlus μ := by
    unfold bfDeltaPlus
    linarith [sqrt_nonneg (9 / 4 + μ)]
  have hminus : 1 / 2 ≤ bfDeltaMinus μ ↔ μ ≤ -(5 / 4 : ℝ) := by
    unfold bfDeltaMinus
    have h : sqrt (9 / 4 + μ) ≤ 1 ↔ 9 / 4 + μ ≤ 1 ^ 2 :=
      sqrt_le_left (by norm_num)
    constructor
    · intro ht
      have := h.mp (by linarith)
      linarith
    · intro ht
      have := h.mpr (by linarith)
      linarith
  exact ⟨fun h => ⟨h.1, hminus.mp h.2.1⟩, fun h => ⟨h.1, hminus.mpr h.2, hplus⟩⟩

theorem bf_strict_lower_dimension {μ : ℝ} (hμ : μ < -(5 / 4 : ℝ)) :
    1 / 2 < bfDeltaMinus μ := by
  have hs : sqrt (9 / 4 + μ) < 1 := (sqrt_lt' zero_lt_one).mpr (by linarith)
  unfold bfDeltaMinus
  linarith

theorem bf_conformal_mass :
    bfDeltaMinus (-2) = 1 ∧ bfDeltaPlus (-2) = 2 := by
  have hs : sqrt (9 / 4 + (-2 : ℝ)) = 1 / 2 := by
    rw [show (9 / 4 + (-2 : ℝ)) = (1 / 2 : ℝ)^2 by norm_num,
      sqrt_sq (by norm_num)]
  constructor <;> simp only [bfDeltaMinus, bfDeltaPlus, hs] <;> norm_num

theorem radial_affine_null_line {L z₀ : ℝ} (hz₀ : 0 < z₀) (x y : ℝ) :
    ∃ V : Fin 5 → ℝ, adsForm V = 0 ∧
      ∀ a : ℝ, 0 ≤ a →
        let z := (1 / z₀ + a)⁻¹
        poincareEmbed L z (z₀ - z) x y = poincareEmbed L z₀ 0 x y + a • V := by
  let C := -z₀ ^ 2 + x ^ 2 + y ^ 2
  let V : Fin 5 → ℝ :=
    ![(L ^ 2 + C) / 2, L * z₀, L * x, L * y, (L ^ 2 - C) / 2]
  refine ⟨V, ?_, ?_⟩
  · simp [V, adsForm, C]
    ring
  · intro a ha
    let d := 1 / z₀ + a
    have hd : d ≠ 0 := (add_pos_of_pos_of_nonneg (one_div_pos.mpr hz₀) ha).ne'
    have hquad : patchQuad d⁻¹ (z₀ - d⁻¹) x y = C + 2 * z₀ * d⁻¹ := by
      unfold patchQuad C
      ring
    change poincareEmbed L d⁻¹ (z₀ - d⁻¹) x y = _
    ext i
    fin_cases i <;>
      simp [poincareEmbed, hquad, patchQuad, V, C, Pi.add_apply, Pi.smul_apply, d] <;>
      field_simp [hz₀.ne'] <;> ring

def ads4Propagator (σ Δ z t x y : ℝ) : ℝ :=
  OmegaMath.ConformalHalfSpaceKernel.kernel σ Δ z t x y

def ads4Wave (σ L z t x y : ℝ) (f : ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ :=
  (1 / L ^ 2) * (z ^ 2 * (
    deriv (deriv (fun u => f u t x y)) z + σ * deriv (deriv (fun u => f z u x y)) t +
    deriv (deriv (fun u => f z t u y)) x + deriv (deriv (fun u => f z t x u)) y) -
    2 * z * deriv (fun u => f u t x y) z)

open OmegaMath.ConformalHalfSpaceKernel in
theorem ads4_propagator_solves_klein_gordon {σ Δ z t x y : ℝ} (L : ℝ)
    (hσ : σ ^ 2 = 1) (hz : 0 < z) (hs : 0 < denominator σ z t x y) :
    let S := denominator σ z t x y
    let K := ads4Propagator σ Δ z t x y
    let fz := fun u => ads4Propagator σ Δ u t x y
    let ft := fun u => ads4Propagator σ Δ z u x y
    let fx := fun u => ads4Propagator σ Δ z t u y
    let fy := fun u => ads4Propagator σ Δ z t x u
    (HasDerivAt fz (radialSlope Δ z S * K) z ∧
      HasDerivAt (deriv fz) (radialCurvature Δ z S * K) z) ∧
    (HasDerivAt ft (transverseSlope Δ σ t S * K) t ∧
      HasDerivAt (deriv ft) (transverseCurvature Δ σ t S * K) t) ∧
    (HasDerivAt fx (transverseSlope Δ 1 x S * K) x ∧
      HasDerivAt (deriv fx) (transverseCurvature Δ 1 x S * K) x) ∧
    (HasDerivAt fy (transverseSlope Δ 1 y S * K) y ∧
      HasDerivAt (deriv fy) (transverseCurvature Δ 1 y S * K) y) ∧
    ads4Wave σ L z t x y (ads4Propagator σ Δ) =
      ads4MassFromDim L Δ * ads4Propagator σ Δ z t x y := by
  obtain ⟨ht, hx, hy⟩ := coordinateJets (Δ := Δ) hz hs
  refine ⟨radialJet hz hs, ht, hx, hy, ?_⟩
  unfold ads4Wave ads4Propagator ads4MassFromDim
  rw [kernel_equation hσ hz hs]
  ring

open OmegaMath.ConformalHalfSpaceKernel in
private theorem ads4_propagator_boundary_scaling {σ Δ a z t x y : ℝ}
    (ha : 0 < a) (hz : 0 < z) (hs : 0 < denominator σ z t x y) :
    ads4Propagator σ Δ (a * z) (a * t) (a * x) (a * y) =
      a ^ (-Δ) * ads4Propagator σ Δ z t x y :=
  kernel_scaling ha hz hs

theorem ads4_propagator_boundary_limit (Δ t x y : ℝ) (hr : 0 < t ^ 2 + x ^ 2 + y ^ 2) :
    Tendsto (fun z : ℝ => z ^ (-Δ) * ads4Propagator 1 Δ z t x y) (𝓝[>] 0)
      (𝓝 (sqrt (t ^ 2 + x ^ 2 + y ^ 2) ^ (-2 * Δ))) :=
  OmegaMath.ConformalHalfSpaceKernel.kernel_boundary Δ t x y hr

open OmegaMath.ConformalHalfSpaceKernel in
theorem ads4_propagator_boundary_scaling_and_inversion {σ Δ L z t x y : ℝ}
    (dz dt dx dy : ℝ) (hz : 0 < z) (hs : 0 < denominator σ z t x y) :
    let S := denominator σ z t x y
    let dS := denominatorVelocity σ z t x y dz dt dx dy
    (∀ a > 0, ads4Propagator σ Δ (a * z) (a * t) (a * x) (a * y) =
       a ^ (-Δ) * ads4Propagator σ Δ z t x y) ∧
    (0 < inverseCoordinate S z ∧
      denominator σ (inverseCoordinate S z) (inverseCoordinate S t)
        (inverseCoordinate S x) (inverseCoordinate S y) = 1 / S) ∧
    OmegaMath.ConformalHalfSpaceKernel.metric σ L (inverseCoordinate S z)
      (inverseVelocity S dS z dz) (inverseVelocity S dS t dt)
      (inverseVelocity S dS x dx) (inverseVelocity S dS y dy) =
        OmegaMath.ConformalHalfSpaceKernel.metric σ L z dz dt dx dy ∧
    ads4Propagator σ Δ z t x y = inverseCoordinate S z ^ Δ ∧
    (let S' := denominator σ (inverseCoordinate S z) (inverseCoordinate S t)
        (inverseCoordinate S x) (inverseCoordinate S y)
     inverseCoordinate S' (inverseCoordinate S z) = z ∧
       inverseCoordinate S' (inverseCoordinate S t) = t ∧
       inverseCoordinate S' (inverseCoordinate S x) = x ∧
       inverseCoordinate S' (inverseCoordinate S y) = y) := by
  exact ⟨fun _ ha => ads4_propagator_boundary_scaling ha hz hs, inversion_preserves_patch hz hs,
    inversion_metric_pullback dz dt dx dy hz hs, rfl, inversion_involutive hz hs⟩

end D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D
