/- GID: D5/S3/Geometry/PPWaveDiamond
   generality: G
   mirror-B: none(waiver:covered-by-perturbed-causal-order-weyl4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Comparison of circular and hyperbolic Jacobi factors in axial plane-wave diamonds. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
Omega original.

Comparison of circular and hyperbolic Jacobi factors in axial plane-wave diamonds.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.PPWaveDiamond

open Real Set Filter
open scoped Topology

private def cone (t : ℝ) : ℝ := sin t * sinh t
private def parallel (t : ℝ) : ℝ := cos t * cosh t
private def cone' (t : ℝ) : ℝ := cos t * sinh t + sin t * cosh t
private def parallel' (t : ℝ) : ℝ := cos t * sinh t - sin t * cosh t

private theorem cone_pos {t : ℝ} (ht : 0 < t) (hπ : t < π) : 0 < cone t :=
  mul_pos (sin_pos_of_pos_of_lt_pi ht hπ) (sinh_pos_iff.mpr ht)

private theorem hasDerivAt_cone (t : ℝ) : HasDerivAt cone (cone' t) t := by
  exact (hasDerivAt_sin t).mul (hasDerivAt_sinh t)

private theorem hasDerivAt_cone' (t : ℝ) : HasDerivAt cone' (2 * parallel t) t := by
  have h := ((hasDerivAt_cos t).mul (hasDerivAt_sinh t)).add
    ((hasDerivAt_sin t).mul (hasDerivAt_cosh t))
  convert h using 1 <;> first | rfl | (unfold parallel; ring)

private theorem hasDerivAt_parallel (t : ℝ) : HasDerivAt parallel (parallel' t) t := by
  convert (hasDerivAt_cos t).mul (hasDerivAt_cosh t) using 1 <;>
    first | rfl | (unfold parallel'; ring)

private theorem hasDerivAt_parallel' (t : ℝ) : HasDerivAt parallel' (-2 * cone t) t := by
  have h := ((hasDerivAt_cos t).mul (hasDerivAt_sinh t)).sub
    ((hasDerivAt_sin t).mul (hasDerivAt_cosh t))
  convert h using 1 <;> first | rfl | (unfold cone; ring)

private theorem at_right_lt_of_deriv_neg {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hc : ContinuousOn f (Icc 0 t))
    (hd : ∀ s ∈ Ioo 0 t, deriv f s < 0) : f t < f 0 := by
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) t) hc
    (fun s hs => hd s (by simpa only [interior_Icc] using hs))
  exact hanti ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht

private theorem at_left_lt_of_deriv_pos {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hc : ContinuousOn f (Icc 0 t))
    (hd : ∀ s ∈ Ioo 0 t, 0 < deriv f s) : f 0 < f t := by
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) t) hc
    (fun s hs => hd s (by simpa only [interior_Icc] using hs))
  exact hmono ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht

private theorem parallel'_neg {t : ℝ} (ht : 0 < t) (hπ : t < π) : parallel' t < 0 := by
  suffices h : parallel' t < parallel' 0 by simpa [parallel'] using h
  apply at_right_lt_of_deriv_neg ht
    (fun x _ => (hasDerivAt_parallel' x).continuousAt.continuousWithinAt)
  intro s hs
  rw [(hasDerivAt_parallel' s).deriv]
  exact mul_neg_of_neg_of_pos (by norm_num) (cone_pos hs.1 (hs.2.trans hπ))

/-- The product of the parallel Jacobi factors lies below its zero-curvature value. -/
theorem parallel_lt_one {t : ℝ} (ht : 0 < t) (hπ : t < π) : cos t * cosh t < 1 := by
  suffices h : parallel t < parallel 0 by simpa [parallel] using h
  apply at_right_lt_of_deriv_neg ht
    (fun x _ => (hasDerivAt_parallel x).continuousAt.continuousWithinAt)
  intro s hs
  rw [(hasDerivAt_parallel s).deriv]
  exact parallel'_neg hs.1 (hs.2.trans hπ)

private def deficit (t : ℝ) : ℝ := t ^ 2 - cone t
private def deficit' (t : ℝ) : ℝ := 2 * t - cone' t

private theorem hasDerivAt_deficit (t : ℝ) : HasDerivAt deficit (deficit' t) t := by
  convert ((hasDerivAt_id t).pow 2).sub (hasDerivAt_cone t) using 1 <;>
    first | rfl | (unfold deficit'; simp)

private theorem hasDerivAt_deficit' (t : ℝ) : HasDerivAt deficit' (2 * (1 - parallel t)) t := by
  have h := ((hasDerivAt_id t).const_mul 2).sub (hasDerivAt_cone' t)
  have he : ((fun y : ℝ => 2 * id y) - cone') = deficit' := by
    ext y
    simp [deficit', mul_comm]
  rw [he] at h
  convert h using 1
  simp
  ring

private theorem deficit'_pos {t : ℝ} (ht : 0 < t) (hπ : t < π) : 0 < deficit' t := by
  suffices h : deficit' 0 < deficit' t by simpa [deficit', cone'] using h
  apply at_left_lt_of_deriv_pos ht
    (fun x _ => (hasDerivAt_deficit' x).continuousAt.continuousWithinAt)
  intro s hs
  rw [(hasDerivAt_deficit' s).deriv]
  exact mul_pos (by norm_num) (sub_pos.mpr (parallel_lt_one hs.1 (hs.2.trans hπ)))

/-- The product of the vertex Jacobi factors lies below the flat quadratic on the first interval. -/
theorem vertex_lt_sq {t : ℝ} (ht : 0 < t) (hπ : t < π) : sin t * sinh t < t ^ 2 := by
  suffices h : deficit 0 < deficit t by simpa [deficit, cone, sub_pos] using h
  apply at_left_lt_of_deriv_pos ht
    (fun x _ => (hasDerivAt_deficit x).continuousAt.continuousWithinAt)
  intro s hs
  rw [(hasDerivAt_deficit s).deriv]
  exact deficit'_pos hs.1 (hs.2.trans hπ)

/-- The normalized vertex area with its continuous value at zero. -/
private def relativeArea : ℝ → ℝ := Function.update (fun t => cone t / t ^ 2) 0 1

private theorem relativeArea_eq {t : ℝ} (ht : t ≠ 0) :
    relativeArea t = cone t / t ^ 2 := Function.update_of_ne ht ..

private theorem continuousAt_relativeArea_zero : ContinuousAt relativeArea 0 := by
  rw [relativeArea, continuousAt_update_same]
  have hsinh : Tendsto (fun t : ℝ => sinh t / t) (𝓝[≠] 0) (𝓝 1) := by
    simpa [slope_fun_def_field] using (hasDerivAt_sinh (0 : ℝ)).tendsto_slope
  simpa only [one_pow, cone, div_mul_div_comm, ← pow_two] using
    tendsto_sin_div_nhdsNE_zero.mul hsinh

private def logArea (t : ℝ) : ℝ := log (relativeArea t)
private def logArea' (t : ℝ) : ℝ := cos t / sin t + cosh t / sinh t - 2 / t

private theorem logArea_zero : logArea 0 = 0 := by simp [logArea, relativeArea]

private theorem logArea_eq {t : ℝ} (ht : 0 < t) (hπ : t < π) :
    logArea t = log (sin t) + log (sinh t) - 2 * log t := by
  rw [logArea, relativeArea_eq ht.ne', log_div (cone_pos ht hπ).ne' (pow_ne_zero 2 ht.ne'), cone,
    log_mul (sin_pos_of_pos_of_lt_pi ht hπ).ne' (sinh_pos_iff.mpr ht).ne', log_pow]
  norm_num

private theorem hasDerivAt_logArea {t : ℝ} (ht : 0 < t) (hπ : t < π) :
    HasDerivAt logArea (logArea' t) t := by
  have hs := (hasDerivAt_sin t).log (sin_pos_of_pos_of_lt_pi ht hπ).ne'
  have hh := (hasDerivAt_sinh t).log (sinh_pos_iff.mpr ht).ne'
  have h := (hs.add hh).sub ((hasDerivAt_log ht.ne').const_mul 2)
  refine (show HasDerivAt (fun z => log (sin z) + log (sinh z) - 2 * log z)
    (logArea' t) t by
      convert h using 1
      rw [logArea', div_eq_mul_inv (2 : ℝ)]).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht hπ] with z hz
  exact logArea_eq hz.1 hz.2

private theorem deriv_logArea' {t : ℝ} (ht : 0 < t) (hπ : t < π) :
    deriv logArea' t = 2 / t ^ 2 - 1 / (sin t) ^ 2 - 1 / (sinh t) ^ 2 := by
  have hs := (hasDerivAt_cos t).div (hasDerivAt_sin t) (sin_pos_of_pos_of_lt_pi ht hπ).ne'
  have hh := (hasDerivAt_cosh t).div (hasDerivAt_sinh t) (sinh_pos_iff.mpr ht).ne'
  have hi := (hasDerivAt_const t (2 : ℝ)).div (hasDerivAt_id t) ht.ne'
  have h := ((hs.add hh).sub hi).deriv
  change deriv (cos / sin + cosh / sinh - (fun _ => 2) / id) t = _
  rw [h]
  simp only [id_eq, zero_mul, zero_sub, mul_one]
  rw [show -sin t * sin t - cos t * cos t = -1 by linarith [sin_sq_add_cos_sq t],
    show sinh t * sinh t - cosh t * cosh t = -1 by linarith [cosh_sq_sub_sinh_sq t]]
  ring

private theorem deriv2_logArea_neg {t : ℝ} (ht : 0 < t) (hπ : t < π) :
    deriv^[2] logArea t < 0 := by
  have hEq : deriv logArea =ᶠ[𝓝 t] logArea' := by
    filter_upwards [Ioo_mem_nhds ht hπ] with z hz
    exact (hasDerivAt_logArea hz.1 hz.2).deriv
  change deriv (deriv logArea) t < 0
  rw [hEq.deriv_eq, deriv_logArea' ht hπ]
  have hs := sin_pos_of_pos_of_lt_pi ht hπ
  have hh := sinh_pos_iff.mpr ht
  have hG := cone_pos ht hπ
  have hrec : 2 / t ^ 2 < 2 / cone t :=
    div_lt_div_of_pos_left (by norm_num) hG (vertex_lt_sq ht hπ)
  have ham : 2 / cone t ≤ 1 / (sin t) ^ 2 + 1 / (sinh t) ^ 2 := by
    unfold cone
    field_simp
    nlinarith [sq_nonneg (sin t - sinh t)]
  linarith

private theorem logArea_strictConcaveOn : StrictConcaveOn ℝ (Ico 0 π) logArea := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ico 0 π)
  · intro t ht
    by_cases hz : t = 0
    · subst t
      apply ContinuousAt.continuousWithinAt
      exact (continuousAt_log (by simp [relativeArea])).comp continuousAt_relativeArea_zero
    · exact (hasDerivAt_logArea (lt_of_le_of_ne ht.1 (Ne.symm hz)) ht.2).continuousAt
        |>.continuousWithinAt
  · intro t ht
    rw [interior_Ico] at ht
    exact deriv2_logArea_neg ht.1 ht.2

private theorem relativeArea_supermul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hπ : a + b < π) :
    relativeArea (a + b) < relativeArea a * relativeArea b := by
  have hsum : 0 < a + b := add_pos ha hb
  have hA : 0 < a / (a + b) := div_pos ha hsum
  have hB : 0 < b / (a + b) := div_pos hb hsum
  have hab : a / (a + b) + b / (a + b) = 1 := by rw [← add_div, div_self hsum.ne']
  have hmem : a + b ∈ Ico 0 π := ⟨hsum.le, hπ⟩
  have hzero : (0 : ℝ) ∈ Ico 0 π := ⟨le_rfl, pi_pos⟩
  have h1 := logArea_strictConcaveOn.2 hmem hzero hsum.ne' hA hB hab
  have h2 := logArea_strictConcaveOn.2 hmem hzero hsum.ne' hB hA (by linarith)
  simp only [smul_eq_mul, logArea_zero, mul_zero, add_zero] at h1 h2
  rw [div_mul_cancel₀ _ hsum.ne'] at h1 h2
  have h3 := add_lt_add h1 h2
  rw [← add_mul, hab, one_mul] at h3
  have hpos t (ht : 0 < t) (hp : t < π) : 0 < relativeArea t := by
    rw [relativeArea_eq ht.ne']
    exact div_pos (cone_pos ht hp) (sq_pos_of_pos ht)
  unfold logArea at h3
  rw [← log_mul (hpos a ha (by linarith)).ne' (hpos b hb (by linarith)).ne'] at h3
  exact (log_lt_log_iff (hpos _ hsum hπ)
    (mul_pos (hpos a ha (by linarith)) (hpos b hb (by linarith)))).mp h3

/-- The normalized transverse slice factor in the axial diamond. -/
def axialSlice (ω T u : ℝ) : ℝ :=
  sqrt (cone (ω * u) * cone (ω * (T - u)) / cone (ω * T)) / ω

/-- The axial volume in terms of the explicit Jacobi factors. -/
def exactAxialVolume (ω T V : ℝ) : ℝ :=
  π * V ^ 2 * ∫ u in 0..T, axialSlice ω T u

private theorem flatSlice_lt_axialSlice {ω T u : ℝ} (hω : 0 < ω)
    (hu : 0 < u) (huT : u < T) (hπ : ω * T < π) :
    u * (T - u) / T < axialSlice ω T u := by
  have hT : 0 < T := hu.trans huT
  let a := ω * u
  let b := ω * (T - u)
  have ha : 0 < a := mul_pos hω hu
  have hb : 0 < b := mul_pos hω (sub_pos.mpr huT)
  have hs : a + b = ω * T := by dsimp [a, b]; ring
  have hspos : 0 < a + b := add_pos ha hb
  have hsπ : a + b < π := hs ▸ hπ
  have hg : 0 < cone (a + b) := cone_pos hspos hsπ
  have h := relativeArea_supermul ha hb hsπ
  rw [relativeArea_eq hspos.ne', relativeArea_eq ha.ne', relativeArea_eq hb.ne',
    div_mul_div_comm,
    div_lt_div_iff₀ (sq_pos_of_pos hspos) (mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hb))] at h
  have hrad : (a * b / (a + b)) ^ 2 < cone a * cone b / cone (a + b) := by
    rw [div_pow, mul_pow, div_lt_div_iff₀ (sq_pos_of_pos hspos) hg]
    simpa [mul_comm] using h
  have hsq := sqrt_lt_sqrt (sq_nonneg _) hrad
  rw [sqrt_sq (div_nonneg (mul_nonneg ha.le hb.le) hspos.le)] at hsq
  have hstart : a * b / (a + b) = ω * (u * (T - u) / T) := by
    rw [hs]
    dsimp [a, b]
    field_simp
  change a * b / (a + b) < _ at hsq
  rw [hstart, hs] at hsq
  exact (lt_div_iff₀ hω).mpr (by simpa [mul_comm] using hsq)

/-- Integral of the flat normalized transverse slice factor. -/
theorem integral_flatSlice {T : ℝ} (hT : 0 < T) :
    (∫ u in 0..T, u * (T - u) / T) = T ^ 2 / 6 := by
  have int_id : IntervalIntegrable (fun u : ℝ => T * u) MeasureTheory.volume 0 T :=
    (by fun_prop : Continuous (fun u : ℝ => T * u)).intervalIntegrable 0 T
  have int_sq : IntervalIntegrable (fun u : ℝ => u ^ 2) MeasureTheory.volume 0 T :=
    (by fun_prop : Continuous (fun u : ℝ => u ^ 2)).intervalIntegrable 0 T
  simp only [show ∀ u : ℝ, u * (T - u) = T * u - u ^ 2 by intro u; ring,
    intervalIntegral.integral_div, intervalIntegral.integral_sub int_id int_sq,
    integral_pow]
  rw [intervalIntegral.integral_const_mul, integral_id]
  field_simp [hT.ne']
  ring

/-- The exact axial slice integral exceeds the flat Minkowski value before the first caustic. -/
theorem axialVolume_strict_excess {ω T V : ℝ} (hω : 0 < ω) (hT : 0 < T)
    (hπ : ω * T < π) (hV : 0 < V) : π * V ^ 2 * T ^ 2 / 6 < exactAxialVolume ω T V := by
  have hc : Continuous (axialSlice ω T) := by
    unfold axialSlice cone
    fun_prop
  let flat : ℝ → ℝ := fun u => u * (T - u) / T
  have hflat : Continuous flat := by dsimp [flat]; fun_prop
  have hle u (hu : u ∈ Ioc 0 T) : flat u ≤ axialSlice ω T u := by
    rcases hu.2.lt_or_eq with huT | rfl
    · exact (flatSlice_lt_axialSlice hω hu.1 huT hπ).le
    · simp [flat, axialSlice, cone]
  have hlt : ∃ u ∈ Icc 0 T, flat u < axialSlice ω T u :=
    ⟨T / 2, ⟨by linarith, by linarith⟩, flatSlice_lt_axialSlice hω (by linarith) (by linarith) hπ⟩
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hT
    hflat.continuousOn hc.continuousOn hle hlt
  rw [show (∫ u in 0..T, flat u) = T ^ 2 / 6 from integral_flatSlice hT] at h
  have hm := mul_lt_mul_of_pos_left h (mul_pos pi_pos (sq_pos_of_pos hV))
  simpa [exactAxialVolume, mul_div_assoc] using hm

end Omega.PPWaveDiamond
