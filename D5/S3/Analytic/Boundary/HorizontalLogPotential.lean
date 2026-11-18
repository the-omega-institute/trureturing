/- GID: D5/S3/Analytic/Boundary/HorizontalLogPotential
   generality: G
   mirror-B: D5/B/S3/Analytic/Boundary/HorizontalLogPotential
   mirror-E: none(waiver:one-dimensional-singular-log-potential)
   anchors: []
   utility: none
   digest: Signed logarithmic height transport through zero and the uniform 2*pi bound. -/

import Mathlib.Analysis.SpecialFunctions.Integrability.Log
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Horizontal squared-log potential

The explicit spatial primitive is continuous in height at zero and has height
derivative `2 * arctan ((x - beta) / t)` away from zero. Its endpoint difference
is the actual logarithmic integral also at zero, by the all-endpoint `integral_log`.
FTC on the two closed half-lines then gives transport for every pair of heights.
No height derivative at zero and no complex logarithmic integral is used.

Repository searches for `logPotential`, `horizontalKernel`, squared-log transport
and singular height transport found no supplier for this inference. Pinned
Mathlib supplies `MeromorphicOn.intervalIntegrable_log`, `Real.log_pow`,
`integral_log`, `integral_div_sq_add_sq` and the interval FTC directly used here.
The elementary integrability, arctangent rewrite, derivative normalization and
norm estimate are consumed helpers; the all-domain transport is the substantive
inference. This is a general real analytic result, not a finite computation,
a generic holomorphic factorization theorem or an RH conclusion.
-/

open Filter MeasureTheory Set
open scoped Interval Topology

set_option autoImplicit false

namespace D5.S3.Analytic.Boundary.HorizontalLogPotential

noncomputable section

/-- The horizontal integral of the squared-distance logarithm. -/
def logPotential (a b beta t : ℝ) : ℝ :=
  ∫ x in a..b, Real.log ((x - beta) ^ 2 + t ^ 2)

/-- The real height kernel, using Lean's division at zero. -/
def horizontalKernel (beta x t : ℝ) : ℝ :=
  2 * t / ((x - beta) ^ 2 + t ^ 2)

private def spatialPrimitive (beta t x : ℝ) : ℝ :=
  let y := x - beta
  y * Real.log (y ^ 2 + t ^ 2) - 2 * y + 2 * t * Real.arctan (y / t)

private theorem logPotential_intervalIntegrable (a b beta t : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log ((x - beta) ^ 2 + t ^ 2)) volume a b := by
  have hf : AnalyticOnNhd ℝ (fun x : ℝ => (x - beta) ^ 2 + t ^ 2) Set.univ := by
    fun_prop
  have hi := ((show MeromorphicOn (fun x : ℝ => (x - beta) ^ 2 + t ^ 2) [[a, b]] from
      fun x hx => hf.meromorphicOn x (Set.mem_univ x))
      |>.intervalIntegrable_log (a := a) (b := b))
  exact hi.congr (fun x hx => rfl)

private theorem spatialPrimitive_hasDerivAt_x {beta t x : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun z : ℝ => spatialPrimitive beta t z)
      (Real.log ((x - beta) ^ 2 + t ^ 2)) x := by
  let y := x - beta
  have hden : y ^ 2 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg y, sq_pos_of_ne_zero ht]
  have hy : HasDerivAt (fun z : ℝ => z - beta) 1 x := by
    simpa using (hasDerivAt_id x).sub_const beta
  have hq : HasDerivAt (fun z : ℝ => (z - beta) ^ 2 + t ^ 2)
      (2 * (x - beta)) x := by
    convert (hy.pow 2).add_const (t ^ 2) using 1
    ring
  have hlog := hq.log hden
  have har : HasDerivAt (fun z : ℝ => Real.arctan ((z - beta) / t))
      ((1 / (1 + ((x - beta) / t) ^ 2)) * (1 / t)) x := by
    exact (Real.hasDerivAt_arctan ((x - beta) / t)).comp x (hy.div_const t)
  have hfirst := hy.mul hlog
  have hlast := har.const_mul (2 * t)
  have hmid := hy.const_mul 2
  have hsum := hfirst.sub hmid |>.add hlast
  convert hsum using 1
  · funext z
    simp only [spatialPrimitive, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
  · field_simp [ht, hden]
    ring

private theorem spatialPrimitive_hasDerivAt_height {beta x t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => spatialPrimitive beta s x)
      (2 * Real.arctan ((x - beta) / t)) t := by
  let y := x - beta
  have hden : y ^ 2 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg y, sq_pos_of_ne_zero ht]
  have hy : HasDerivAt (fun s : ℝ => y ^ 2 + s ^ 2) (2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).const_add (y ^ 2) using 1 <;> simp
  have hlog := hy.log hden
  have hquot : HasDerivAt (fun s : ℝ => y / s) (-y / t ^ 2) t := by
    convert (hasDerivAt_id t).inv ht |>.const_mul y using 1 <;> simp [div_eq_mul_inv]
  have har := (Real.hasDerivAt_arctan (y / t)).comp t hquot
  have hfirst := (hasDerivAt_const t y).mul hlog
  have hlast := ((hasDerivAt_id t).mul har).const_mul 2
  have hmid : HasDerivAt (fun _ : ℝ => 2 * y) 0 t := hasDerivAt_const t (2 * y)
  have hsum := hfirst.sub hmid |>.add hlast
  convert hsum using 1
  · funext s
    dsimp only [spatialPrimitive, y, Pi.sub_apply, Pi.add_apply, Pi.mul_apply,
      id_eq, Function.comp_apply]
    ring
  · dsimp only [id_eq, Function.comp_apply]
    field_simp [ht, hden]
    ring

private theorem horizontalKernel_integral_eq_arctan (a b beta t : ℝ) :
    (∫ x in a..b, horizontalKernel beta x t) =
      2 * (Real.arctan ((b - beta) / t) - Real.arctan ((a - beta) / t)) := by
  have hfun : (fun x : ℝ => horizontalKernel beta x t) =
      (fun x : ℝ => 2 * (t / ((x - beta) ^ 2 + t ^ 2))) := by
    funext x
    simp only [horizontalKernel]
    ring
  rw [hfun, intervalIntegral.integral_const_mul]
  have hshift :
      (∫ x in a..b, t / ((x - beta) ^ 2 + t ^ 2)) =
        ∫ y in a - beta..b - beta, t / (t ^ 2 + y ^ 2) := by
    rw [← intervalIntegral.integral_comp_sub_right]
    congr 1
    funext x
    ring
  rw [hshift, integral_div_sq_add_sq]

private theorem logPotential_eq_primitive_sub (a b : ℝ) (hab : a ≤ b) (beta t : ℝ) :
    logPotential a b beta t = spatialPrimitive beta t b - spatialPrimitive beta t a := by
  by_cases ht : t = 0
  · subst t
    simp only [logPotential, zero_pow (by decide : 2 ≠ 0), add_zero,
      spatialPrimitive, mul_zero, zero_mul]
    rw [intervalIntegral.integral_comp_sub_right (fun y : ℝ => Real.log (y ^ 2)) beta]
    have hlog : (fun y : ℝ => Real.log (y ^ 2)) =
        (fun y : ℝ => 2 * Real.log y) := by
      funext y
      rw [Real.log_pow]
      norm_num
    rw [hlog, intervalIntegral.integral_const_mul, integral_log]
    simp only [Real.log_pow, Nat.cast_ofNat]
    ring
  · unfold logPotential
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    · exact fun x hx =>
        (spatialPrimitive_hasDerivAt_x (beta := beta) (x := x) ht).continuousAt.continuousWithinAt
    · intro x hx
      exact spatialPrimitive_hasDerivAt_x ht
    · exact logPotential_intervalIntegrable a b beta t

private theorem spatialPrimitive_continuousAt_zero (beta x : ℝ) :
    ContinuousAt (fun t : ℝ => spatialPrimitive beta t x) 0 := by
  let y := x - beta
  by_cases hy : y = 0
  · change x - beta = 0 at hy
    simpa [spatialPrimitive, hy] using
      (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) 0)
  · have harg : ContinuousAt (fun t : ℝ => y ^ 2 + t ^ 2) 0 := by
      fun_prop
    have harg0 : y ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by
      simpa using pow_ne_zero 2 hy
    have hlog : ContinuousAt (fun t : ℝ => Real.log (y ^ 2 + t ^ 2)) 0 :=
      harg.log harg0
    have hbound : IsBoundedUnder (· ≤ ·) (𝓝 (0 : ℝ))
        (Norm.norm ∘ fun t : ℝ => Real.arctan (y / t)) := by
      apply Filter.isBoundedUnder_of_eventually_le (a := Real.pi / 2)
      filter_upwards [] with s
      change ‖Real.arctan (y / s)‖ ≤ Real.pi / 2
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [Real.arctan_lt_pi_div_two (y / s),
        Real.neg_pi_div_two_lt_arctan (y / s), Real.pi_pos]
    have hprod : Tendsto (fun t : ℝ => t * Real.arctan (y / t))
        (𝓝 0) (𝓝 0) :=
      Filter.Tendsto.zero_mul_isBoundedUnder_le
        (tendsto_id : Tendsto id (nhds (0 : ℝ)) (nhds 0)) hbound
    have hfirst : Tendsto (fun t : ℝ => y * Real.log (y ^ 2 + t ^ 2))
        (𝓝 0) (𝓝 (y * Real.log (y ^ 2))) :=
      by simpa using tendsto_const_nhds.mul hlog
    have hmid : Tendsto (fun _ : ℝ => 2 * y) (𝓝 0) (𝓝 (2 * y)) :=
      tendsto_const_nhds
    have hsum := (hfirst.sub hmid).add (hprod.const_mul 2)
    change Tendsto (fun t : ℝ => spatialPrimitive beta t x) (nhds 0)
      (nhds (spatialPrimitive beta 0 x))
    simpa [spatialPrimitive, y, Real.log_pow, mul_comm,
      mul_left_comm, mul_assoc] using hsum

private theorem logPotential_continuousAt_zero (a b : ℝ) (hab : a ≤ b) (beta : ℝ) :
    ContinuousAt (fun t : ℝ => logPotential a b beta t) 0 := by
  have hP := (spatialPrimitive_continuousAt_zero beta b).sub
    (spatialPrimitive_continuousAt_zero beta a)
  have hEq : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ),
      logPotential a b beta s =
        spatialPrimitive beta s b - spatialPrimitive beta s a :=
    Filter.Eventually.of_forall (fun s => logPotential_eq_primitive_sub a b hab beta s)
  exact hP.congr_of_eventuallyEq hEq

private theorem abs_horizontalKernel_integral_le (a b beta t : ℝ) :
    |∫ x in a..b, horizontalKernel beta x t| ≤ 2 * Real.pi := by
  rw [horizontalKernel_integral_eq_arctan, abs_le]
  constructor <;> nlinarith [Real.arctan_lt_pi_div_two ((b - beta) / t),
    Real.neg_pi_div_two_lt_arctan ((b - beta) / t),
    Real.arctan_lt_pi_div_two ((a - beta) / t),
    Real.neg_pi_div_two_lt_arctan ((a - beta) / t)]

private theorem vertical_derivative_intervalIntegrable (a b beta u v : ℝ) :
    IntervalIntegrable (fun t : ℝ => ∫ x in a..b, horizontalKernel beta x t)
      volume u v := by
  have hm : Measurable (fun t : ℝ => ∫ x in a..b, horizontalKernel beta x t) := by
    have heq : (fun t : ℝ => ∫ x in a..b, horizontalKernel beta x t) =
        (fun t : ℝ => 2 * (Real.arctan ((b - beta) / t) -
          Real.arctan ((a - beta) / t))) :=
      funext fun t => horizontalKernel_integral_eq_arctan a b beta t
    rw [heq]
    fun_prop
  apply intervalIntegrable_iff.mpr
  refine (intervalIntegrable_const (a := u) (b := v) (c := 2 * Real.pi)).def'.mono'
    hm.aestronglyMeasurable ?_
  filter_upwards [] with t
  simpa only [Real.norm_eq_abs] using abs_horizontalKernel_integral_le a b beta t

private theorem logPotential_hasDerivAt_off_zero (a b : ℝ) (hab : a ≤ b)
    (beta : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => logPotential a b beta s)
      (∫ x in a..b, horizontalKernel beta x t) t := by
  have hP := (spatialPrimitive_hasDerivAt_height (beta := beta) (x := b) ht).sub
    (spatialPrimitive_hasDerivAt_height (beta := beta) (x := a) ht)
  have heq : (fun s : ℝ => logPotential a b beta s) =
      (fun s : ℝ => spatialPrimitive beta s b - spatialPrimitive beta s a) :=
    funext fun s => logPotential_eq_primitive_sub a b hab beta s
  rw [heq, horizontalKernel_integral_eq_arctan]
  convert hP using 1
  ring

private theorem logPotential_continuous (a b : ℝ) (hab : a ≤ b) (beta : ℝ) :
    Continuous (fun t : ℝ => logPotential a b beta t) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    exact logPotential_continuousAt_zero a b hab beta
  · exact (logPotential_hasDerivAt_off_zero a b hab beta ht).continuousAt

/-- Exact signed height transport, including intervals crossing zero. -/
theorem logPotential_signed_transport (a b : ℝ) (hab : a ≤ b) (beta u v : ℝ) :
    logPotential a b beta v - logPotential a b beta u =
      ∫ t in u..v, ∫ x in a..b, horizontalKernel beta x t := by
  let K := fun t : ℝ => ∫ x in a..b, horizontalKernel beta x t
  have hbase : ∀ w : ℝ, (∫ t in 0..w, K t) =
      logPotential a b beta w - logPotential a b beta 0 := by
    intro w
    rcases le_total 0 w with hw | hw
    · apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hw
      · exact (logPotential_continuous a b hab beta).continuousOn
      · intro t ht
        exact logPotential_hasDerivAt_off_zero a b hab beta (ne_of_gt ht.1)
      · exact vertical_derivative_intervalIntegrable a b beta 0 w
    · have hn : (∫ t in w..0, K t) =
          logPotential a b beta 0 - logPotential a b beta w := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hw
        · exact (logPotential_continuous a b hab beta).continuousOn
        · intro t ht
          exact logPotential_hasDerivAt_off_zero a b hab beta (ne_of_lt ht.2)
        · exact vertical_derivative_intervalIntegrable a b beta w 0
      rw [intervalIntegral.integral_symm, hn]
      ring
  have hglue := intervalIntegral.integral_add_adjacent_intervals
    (vertical_derivative_intervalIntegrable a b beta u 0)
    (vertical_derivative_intervalIntegrable a b beta 0 v)
  change (∫ t in u..0, K t) + (∫ t in 0..v, K t) = (∫ t in u..v, K t) at hglue
  change _ = ∫ t in u..v, K t
  rw [← hglue]
  have hsymm : (∫ t in u..0, K t) = -(∫ t in 0..u, K t) := by
    rw [intervalIntegral.integral_symm]
  rw [hsymm, hbase u, hbase v]
  ring

/-- The uniform height bound for the squared-distance log potential. -/
theorem logPotential_lipschitz (a b : ℝ) (hab : a ≤ b) (beta u v : ℝ) :
    |logPotential a b beta v - logPotential a b beta u| ≤
      2 * Real.pi * |v - u| := by
  rw [logPotential_signed_transport a b hab beta u v]
  simpa only [Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := u) (b := v) (C := 2 * Real.pi)
      (f := fun t : ℝ => ∫ x in a..b, horizontalKernel beta x t)
      (fun t ht => by
        simpa only [Real.norm_eq_abs] using abs_horizontalKernel_integral_le a b beta t))

end
end D5.S3.Analytic.Boundary.HorizontalLogPotential
