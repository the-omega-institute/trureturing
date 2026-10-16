/- GID: D5/S3/Observer/Linear/PositiveWindowObservationBound
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/PositiveWindowObservationBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite uniform derivative floor gives an explicit observation-energy floor on every positive window in arbitrary Hilbert spaces. -/

import D5.S3.Observer.Linear.HilbertMomentCoercivity
import D5.S3.Observer.Linear.ExactTaylorObservationRemainder
import Mathlib.Analysis.Normed.Module.RCLike.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Linear.PositiveWindowObservationBound

open MeasureTheory Finset
open scoped BigOperators
open D5.S3.Observer.Linear.HilbertMomentCoercivity
open D5.S3.Observer.Linear.ExactTaylorObservationRemainder

variable {𝕜 V W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V] [Nontrivial V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-- The actual squared observation trajectory norm on a time interval. -/
def trajectoryEnergy (B : V →L[𝕜] V) (C : V →L[𝕜] W) (T : ℝ) (x : V) : ℝ :=
  ∫ t in (0 : ℝ)..T, ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x)‖ ^ 2

/-- Uniform observation energy, defined by the unit-sphere infimum. -/
def observationFloor (B : V →L[𝕜] V) (C : V →L[𝕜] W) (T : ℝ) : ℝ :=
  sInf (trajectoryEnergy B C T '' {x : V | ‖x‖ = 1})

/-- Uniform finite derivative energy, with the zeroth derivative included. -/
def derivativeFloor (B : V →L[𝕜] V) (C : V →L[𝕜] W) (N : ℕ) : ℝ :=
  sInf ((fun x : V => ∑ i : Fin (N + 1), ‖C ((B ^ (i : ℕ)) x)‖ ^ 2) ''
    {x : V | ‖x‖ = 1})

/-- The leading polynomial scale. -/
def derivativeScale (N : ℕ) (μ : ℝ) : ℝ :=
  Real.sqrt (hilbertEigenvalue N * μ) / (N.factorial : ℝ)

/-- The exact unit-window Taylor-tail constant. -/
def remainderScale (B : V →L[𝕜] V) (C : V →L[𝕜] W) (N : ℕ) : ℝ :=
  ‖C‖ * Real.exp (max 1 ‖B‖) * max 1 ‖B‖ ^ (N + 1) /
    (((N + 1).factorial : ℝ) * Real.sqrt (2 * N + 3 : ℕ))

/-- A positive cutoff on which the error is at most half the leading scale. -/
def windowCutoff (B : V →L[𝕜] V) (C : V →L[𝕜] W) (N : ℕ) (μ : ℝ) : ℝ :=
  min 1 (derivativeScale N μ / (2 * remainderScale B C N))

/-- The explicit coefficient in the observation-energy lower bound. -/
def windowCoefficient (N : ℕ) (μ : ℝ) : ℝ :=
  hilbertEigenvalue N * μ / (4 * (N.factorial : ℝ) ^ 2)

private theorem unit_sphere_nonempty (𝕜 : Type*) [RCLike 𝕜] {V : Type*}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [Nontrivial V] : ({x : V | ‖x‖ = 1} : Set V).Nonempty := by
  obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty_rclike 𝕜 (E := V) (r := 1) (by norm_num)
  exact ⟨x, by simpa using hx⟩

private theorem continuous_trajectory (B : V →L[𝕜] V) (C : V →L[𝕜] W) (x : V) :
    Continuous (fun t : ℝ => C ((NormedSpace.exp ((t : 𝕜) • B)) x)) := by
  exact C.continuous.comp
    ((ContinuousLinearMap.apply 𝕜 V x).continuous.comp
      ((continuous_iff_continuousAt.mpr (fun z =>
        (NormedSpace.exp_analytic (𝕂 := 𝕜) z).continuousAt)).comp
        ((RCLike.continuous_ofReal : Continuous (fun t : ℝ => (t : 𝕜))).smul
          continuous_const)))

private theorem derivative_floor_le (B : V →L[𝕜] V) (C : V →L[𝕜] W)
    (N : ℕ) (x : V) (hx : ‖x‖ = 1) :
    derivativeFloor B C N ≤ ∑ i : Fin (N + 1), ‖C ((B ^ (i : ℕ)) x)‖ ^ 2 := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨y, _, rfl⟩; exact sum_nonneg (fun _ _ => sq_nonneg _)⟩
  · exact ⟨x, hx, rfl⟩

private theorem constants_positive (B : V →L[𝕜] V) (C : V →L[𝕜] W)
    (N : ℕ) (μ : ℝ) (hμ : 0 < μ) (hfloor : μ ≤ derivativeFloor B C N) :
    0 < derivativeScale N μ ∧ 0 < remainderScale B C N ∧
    0 < windowCutoff B C N μ ∧ 0 < windowCoefficient N μ := by
  have hlam : 0 < hilbertEigenvalue N := (hilbert_polynomial_coercivity N
    (fun _ : Fin (N + 1) => (0 : ℝ))).1
  have hC : C ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := unit_sphere_nonempty 𝕜 (V := V)
    have hh := hfloor.trans (derivative_floor_le B C N x hx)
    simp only [hz, ContinuousLinearMap.zero_apply, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero] at hh
    linarith
  have hb : 0 < max 1 ‖B‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hd : 0 < derivativeScale N μ := by
    unfold derivativeScale
    exact div_pos (Real.sqrt_pos.2 (mul_pos hlam hμ)) (by positivity)
  have hr : 0 < remainderScale B C N := by
    unfold remainderScale
    exact div_pos (mul_pos (mul_pos (norm_pos_iff.mpr hC) (Real.exp_pos _))
      (pow_pos hb _)) (mul_pos (by positivity) (Real.sqrt_pos.2 (by positivity)))
  exact ⟨hd, hr, lt_min zero_lt_one (div_pos hd (mul_pos (by norm_num) hr)),
    div_pos (mul_pos hlam hμ) (by positivity)⟩

private theorem small_window_floor (B : V →L[𝕜] V) (C : V →L[𝕜] W)
    (N : ℕ) (μ : ℝ) (hμ : 0 < μ) (hfloor : μ ≤ derivativeFloor B C N)
    (T : ℝ) (hT : 0 < T) (hcut : T ≤ windowCutoff B C N μ)
    (x : V) (hx : ‖x‖ = 1) :
    windowCoefficient N μ * T ^ (2 * N + 1) ≤ trajectoryEnergy B C T x := by
  have hT1 : T ≤ 1 := hcut.trans (min_le_left _ _)
  have hlam : 0 < hilbertEigenvalue N := (hilbert_polynomial_coercivity N
    (fun _ : Fin (N + 1) => (0 : ℝ))).1
  have hconst := constants_positive B C N μ hμ hfloor
  have hsum : μ ≤ ∑ i : Fin (N + 1), ‖C ((B ^ (i : ℕ)) x)‖ ^ 2 :=
    hfloor.trans (derivative_floor_le B C N x hx)
  have hpoly := taylor_polynomial_energy_floor (𝕜 := 𝕜) N
    (fun i : Fin (N + 1) => C ((B ^ (i : ℕ)) x)) T hT hT1
  have hpolyeq (t : ℝ) :
      (∑ i : Fin (N + 1),
        (((t ^ (i : ℕ) / ((i : ℕ).factorial : ℝ)) : ℝ) : 𝕜) •
          C ((B ^ (i : ℕ)) x)) = observationTaylor B C N t x := by
    unfold observationTaylor
    exact Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      (((t ^ k / (k.factorial : ℝ)) : ℝ) : 𝕜) • C ((B ^ k) x)) (N + 1)
  simp_rw [hpolyeq] at hpoly
  have hmain : derivativeScale N μ ^ 2 * T ^ (2 * N + 1) ≤
      ∫ t in (0 : ℝ)..T, ‖observationTaylor B C N t x‖ ^ 2 := by
    calc
      _ = hilbertEigenvalue N * T ^ (2 * N + 1) / (N.factorial : ℝ) ^ 2 * μ := by
        unfold derivativeScale
        rw [div_pow, Real.sq_sqrt (mul_nonneg hlam.le hμ.le)]
        ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hsum (by positivity)).trans hpoly
  have herr := observation_taylor_energy_remainder B C N T hT.le x
  rw [hx, one_pow, mul_one] at herr
  have htail : (∫ t in (0 : ℝ)..T,
      ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x) - observationTaylor B C N t x‖ ^ 2) ≤
      remainderScale B C N ^ 2 * T ^ (2 * N + 3) := by
    calc
      _ ≤ _ := herr
      _ ≤ (‖C‖ * Real.exp (max 1 ‖B‖) * max 1 ‖B‖ ^ (N + 1) /
          ((N + 1).factorial : ℝ)) ^ 2 *
          (T ^ (2 * N + 3) / (2 * N + 3 : ℕ)) := by
        gcongr
        exact mul_le_of_le_one_right (le_trans (by norm_num) (le_max_left _ _)) hT1
      _ = _ := by
        unfold remainderScale
        simp only [div_pow, mul_pow,
          Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (2 * N + 3 : ℕ))]
        ring
  have hcut' : T ≤ derivativeScale N μ / (2 * remainderScale B C N) :=
    hcut.trans (min_le_right _ _)
  have hrt : remainderScale B C N * T ≤ derivativeScale N μ / 2 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num) hconst.2.1)).mp hcut'
    linarith
  have htail' : (∫ t in (0 : ℝ)..T,
      ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x) - observationTaylor B C N t x‖ ^ 2) ≤
      derivativeScale N μ ^ 2 * T ^ (2 * N + 1) / 4 := by
    have hs := mul_self_le_mul_self (mul_nonneg hconst.2.1.le hT.le) hrt
    have hp : T ^ (2 * N + 3) = T ^ 2 * T ^ (2 * N + 1) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      _ ≤ remainderScale B C N ^ 2 * T ^ (2 * N + 3) := htail
      _ = (remainderScale B C N * T) ^ 2 * T ^ (2 * N + 1) := by rw [hp]; ring
      _ ≤ (derivativeScale N μ / 2) ^ 2 * T ^ (2 * N + 1) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hs]) (pow_nonneg hT.le _)
      _ = _ := by ring
  have hc := continuous_trajectory B C x
  have hp : Continuous (fun t : ℝ => observationTaylor B C N t x) := by
    unfold observationTaylor
    fun_prop
  have hpoint (t : ℝ) : ‖observationTaylor B C N t x‖ ^ 2 ≤
      2 * ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x)‖ ^ 2 +
      2 * ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x) - observationTaylor B C N t x‖ ^ 2 := by
    have hn := norm_sub_le (C ((NormedSpace.exp ((t : 𝕜) • B)) x))
      (C ((NormedSpace.exp ((t : 𝕜) • B)) x) - observationTaylor B C N t x)
    rw [sub_sub_cancel] at hn
    have hnon := norm_nonneg (observationTaylor B C N t x)
    nlinarith [sq_nonneg (‖C ((NormedSpace.exp ((t : 𝕜) • B)) x)‖ -
      ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x) - observationTaylor B C N t x‖)]
  have hi := intervalIntegral.integral_mono_on (μ := volume) hT.le
    ((hp.norm.pow 2).intervalIntegrable 0 T)
    ((((hc.norm.pow 2).const_mul 2).add
      (((hc.sub hp).norm.pow 2).const_mul 2)).intervalIntegrable 0 T)
    (fun t _ => hpoint t)
  dsimp only [Pi.add_apply, Pi.pow_apply, Pi.sub_apply] at hi
  have hfi : IntervalIntegrable (fun t : ℝ =>
      2 * ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x)‖ ^ 2) volume 0 T :=
    ((hc.norm.pow 2).const_mul 2).intervalIntegrable 0 T
  have hgi : IntervalIntegrable (fun t : ℝ =>
      2 * ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x) - observationTaylor B C N t x‖ ^ 2)
      volume 0 T := (((hc.sub hp).norm.pow 2).const_mul 2).intervalIntegrable 0 T
  rw [intervalIntegral.integral_add hfi hgi,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  have halpha : windowCoefficient N μ = derivativeScale N μ ^ 2 / 4 := by
    unfold windowCoefficient derivativeScale
    rw [div_pow, Real.sq_sqrt (mul_nonneg hlam.le hμ.le)]
    ring
  rw [halpha]
  change _ ≤ ∫ t in (0 : ℝ)..T, ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x)‖ ^ 2
  linarith

/-- Every positive window has the explicit uniform observation lower bound
forced by a finite positive derivative floor. No infimum attainment or
finite-dimensional hypothesis is used. -/
theorem positive_window_observation_bound
    (B : V →L[𝕜] V) (C : V →L[𝕜] W) (N : ℕ) (μ : ℝ)
    (hμ : 0 < μ) (hfloor : μ ≤ derivativeFloor B C N) (T : ℝ) (hT : 0 < T) :
    0 < remainderScale B C N ∧ 0 < windowCutoff B C N μ ∧
    windowCoefficient N μ * min T (windowCutoff B C N μ) ^ (2 * N + 1) ≤
      observationFloor B C T ∧
    0 < windowCoefficient N μ * min T (windowCutoff B C N μ) ^ (2 * N + 1) := by
  have hc := constants_positive B C N μ hμ hfloor
  have ht : 0 < min T (windowCutoff B C N μ) := lt_min hT hc.2.2.1
  refine ⟨hc.2.1, hc.2.2.1, ?_, mul_pos hc.2.2.2 (pow_pos ht _)⟩
  apply le_csInf ((unit_sphere_nonempty 𝕜 (V := V)).image (trajectoryEnergy B C T))
  rintro _ ⟨x, hx, rfl⟩
  apply (small_window_floor B C N μ hμ hfloor _ ht (min_le_right _ _) x hx).trans
  exact intervalIntegral.integral_mono_interval le_rfl ht.le (min_le_left _ _)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (((continuous_trajectory B C x).norm.pow 2).intervalIntegrable 0 T)

end D5.S3.Observer.Linear.PositiveWindowObservationBound
