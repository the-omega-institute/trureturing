/- GID: D5/S3/VertexAlgebra/Analysis/SmoothCircleFourier
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Analysis/SmoothCircleFourier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual smooth periodic tests have weighted two-sided summable Fourier coefficients. -/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.PSeries
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
We iterate Mathlib's existing circle integration-by-parts theorem, retaining the
periodic endpoint cancellation at every order. No rapid-decay predicate is an
input. The finite constant uses the convergent two-sided inverse-square series;
its evaluation by the Basel formula is unnecessary for the operator consumer.
Fourier and calculus suppliers retain Mathlib's Apache 2.0 attribution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open Complex MeasureTheory Set
namespace D5.S3.VertexAlgebra.Analysis.SmoothCircleFourier

def period : ℝ := 2 * Real.pi
private theorem period_pos : 0 < period := by dsimp [period]; positivity
instance : Fact (0 < period) := ⟨period_pos⟩

/-- Genuine globally smooth lifts of functions on the circle of circumference 2π. -/
structure Test where
  lift : ℝ → ℂ
  smooth : ContDiff ℝ ∞ lift
  periodic : Function.Periodic lift period

namespace Test
variable (f : Test)

def jet (s : ℕ) : ℝ → ℂ := iteratedDeriv s f.lift

private theorem jet_continuous (s : ℕ) : Continuous (f.jet s) :=
  f.smooth.continuous_iteratedDeriv s (by simp)

private theorem jet_hasDerivAt (s : ℕ) (x : ℝ) :
    HasDerivAt (f.jet s) (f.jet (s+1) x) x := by
  change HasDerivAt (iteratedDeriv s f.lift) (iteratedDeriv (s+1) f.lift x) x
  rw [iteratedDeriv_succ]
  have hs : ContDiff ℝ (s+1) f.lift := f.smooth.of_le (by simp)
  exact (hs.differentiable_iteratedDeriv' s x).hasDerivAt

/-- Endpoint cancellation is derived from global periodicity at every derivative. -/
theorem jet_periodic (s : ℕ) : Function.Periodic (f.jet s) period := by
  induction s with
  | zero => simpa [jet] using f.periodic
  | succ s ih =>
    intro x
    have heq : (fun y => f.jet s (y+period)) = f.jet s := funext ih
    have hadd : HasDerivAt (fun y : ℝ => y+period) 1 x := by
      simpa only [id_eq] using (hasDerivAt_id x).add_const period
    have hh : HasDerivAt (fun y => f.jet s (y+period))
        (f.jet (s+1) (x+period)) x := by
      simpa only [Function.comp_def, one_smul] using
        (jet_hasDerivAt f s (x+period)).scomp x hadd
    rw [heq] at hh
    simpa only [mul_one] using hh.unique (jet_hasDerivAt f s x)

def jetCompact (s : ℕ) : C(Icc (0 : ℝ) period, ℂ) :=
  ⟨fun x => f.jet s x, (jet_continuous f s).comp continuous_subtype_val⟩

def jetNorm (s : ℕ) : ℝ := ‖f.jetCompact s‖

private theorem jet_le (s : ℕ) (x : ℝ) (hx : x ∈ Icc 0 period) :
    ‖f.jet s x‖ ≤ f.jetNorm s :=
  (f.jetCompact s).norm_coe_le_norm ⟨x, hx⟩

/-- This interval supplier is exactly the AddCircle convention at period 2π. -/
def coeffJet (s : ℕ) (m : ℤ) : ℂ :=
  fourierCoeffOn period_pos (f.jet s) m

def coefficient (m : ℤ) : ℂ := f.coeffJet 0 m

theorem coefficient_circle (m : ℤ) :
    f.coefficient m = fourierCoeff f.periodic.lift m := by
  rw [coefficient, coeffJet, fourierCoeffOn_eq_integral,
    fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [sub_zero, zero_add, jet, iteratedDeriv_zero, Function.Periodic.lift_coe]
  simp only [fourier_coe_apply, sub_zero]

private theorem coeffJet_norm (s : ℕ) (m : ℤ) : ‖f.coeffJet s m‖ ≤ f.jetNorm s := by
  rw [coeffJet, fourierCoeffOn_eq_integral, norm_smul, Real.norm_eq_abs]
  have hi : ‖∫ x in (0 : ℝ)..period,
      fourier (-m) (x : AddCircle (period-0)) • f.jet s x‖ ≤
      f.jetNorm s * period := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const ?_).trans_eq
      (by rw [sub_zero, abs_of_pos period_pos])
    intro x hx
    have hx' : x ∈ Icc 0 period := by
      rw [uIoc_of_le period_pos.le] at hx
      exact ⟨hx.1.le, hx.2⟩
    simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
      using jet_le f s x hx'
  have hp : 0 < period := period_pos
  calc
    _ ≤ |1 / (period-0)| * (f.jetNorm s * period) :=
      mul_le_mul_of_nonneg_left hi (abs_nonneg _)
    _ = f.jetNorm s := by
      rw [sub_zero, abs_of_pos (by positivity : 0 < 1/period)]
      field_simp

theorem coeffJet_step (s : ℕ) (m : ℤ) (hm : m ≠ 0) :
    f.coeffJet s m = (Complex.I * (m : ℂ))⁻¹ * f.coeffJet (s+1) m := by
  have hh := fourierCoeffOn_of_hasDerivAt period_pos hm
    (fun x _ => jet_hasDerivAt f s x)
    ((jet_continuous f (s+1)).intervalIntegrable 0 period)
  have hend : f.jet s period = f.jet s 0 := by
    simpa only [zero_add] using jet_periodic f s 0
  change f.coeffJet s m = _ at hh
  rw [hend, sub_self, mul_zero, zero_sub] at hh
  rw [hh]
  simp only [coeffJet] at *
  have hn : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [period, sub_zero, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_zero]
  field_simp [hn, hp, Complex.I_ne_zero]
  <;> ring

private theorem coeffJet_iterate (s : ℕ) (m : ℤ) (hm : m ≠ 0) :
    f.coefficient m = ((Complex.I * (m : ℂ))⁻¹)^s * f.coeffJet s m := by
  induction s with
  | zero => simp [coefficient]
  | succ s ih =>
    rw [ih, coeffJet_step f s m hm, pow_succ]
    ring

private theorem coefficient_decay (s : ℕ) (m : ℤ) (hm : m ≠ 0) :
    ‖f.coefficient m‖ ≤ f.jetNorm s / |(m : ℝ)|^s := by
  rw [coeffJet_iterate f s m hm, norm_mul, norm_pow, norm_inv, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_intCast]
  calc
    _ ≤ (|(m : ℝ)|⁻¹)^s * f.jetNorm s :=
      mul_le_mul_of_nonneg_left (coeffJet_norm f s m) (by positivity)
    _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring

def weight (r : ℕ) (m : ℤ) : ℝ := ‖f.coefficient m‖ * (1+|(m : ℝ)|)^r

def W (r : ℕ) : ℝ := ∑' m : ℤ, f.weight r m

theorem weight_nonneg (r : ℕ) (m : ℤ) : 0 ≤ f.weight r m := by
  dsimp [weight]; positivity

private theorem weight_majorant (r : ℕ) (m : ℤ) :
    f.weight r m ≤ (if m = 0 then f.jetNorm 0 else 0) +
      (2^r * f.jetNorm (r+2)) * (1 / (m : ℝ)^2) := by
  by_cases hm : m = 0
  · subst m
    simpa [weight, coefficient] using coeffJet_norm f 0 0
  · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have ha : 0 < |(m : ℝ)| := abs_pos.mpr hmR
    have ha1 : 1 ≤ |(m : ℝ)| := by
      have hn : 1 ≤ m.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hm)
      have hz : (1 : ℤ) ≤ |m| := by simpa only [Int.natCast_natAbs] using (show (1 : ℤ) ≤ (m.natAbs : ℤ) by exact_mod_cast hn)
      exact_mod_cast hz
    have hp : (1+|(m : ℝ)|)^r ≤ (2*|(m : ℝ)|)^r :=
      pow_le_pow_left₀ (by positivity) (by linarith) r
    have hd := coefficient_decay f (r+2) m hm
    simp only [weight, if_neg hm, zero_add]
    calc
      _ ≤ (f.jetNorm (r+2) / |(m : ℝ)|^(r+2)) * (2*|(m : ℝ)|)^r :=
        mul_le_mul hd hp (by positivity) (by have hM : 0 ≤ f.jetNorm (r+2) := norm_nonneg _; positivity)
      _ = _ := by
        rw [mul_pow, pow_add, sq_abs]
        field_simp [hmR, ha.ne']

theorem weighted_summable (r : ℕ) : Summable (f.weight r) := by
  classical
  have hsingle : Summable (fun m : ℤ => if m = 0 then f.jetNorm 0 else 0) :=
    summable_of_ne_finset_zero (s := {0}) (by intro m hm; simp at hm; simp [hm])
  have hp : Summable (fun m : ℤ => 1 / (m : ℝ)^2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  exact Summable.of_nonneg_of_le (weight_nonneg f r) (weight_majorant f r)
    (hsingle.add (hp.mul_left (2^r * f.jetNorm (r+2))))

/-- A finite, correctly proved smooth-test bound, without needing the Basel evaluation. -/
private theorem W_le (r : ℕ) :
    f.W r ≤ f.jetNorm 0 + (2^r * f.jetNorm (r+2)) *
      (∑' m : ℤ, 1 / (m : ℝ)^2) := by
  classical
  have hsingle : Summable (fun m : ℤ => if m = 0 then f.jetNorm 0 else 0) :=
    summable_of_ne_finset_zero (s := {0}) (by intro m hm; simp at hm; simp [hm])
  have hp : Summable (fun m : ℤ => 1 / (m : ℝ)^2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have h := (weighted_summable f r).tsum_le_tsum (weight_majorant f r)
    (hsingle.add (hp.mul_left (2^r * f.jetNorm (r+2))))
  simpa only [W, hsingle.tsum_add (hp.mul_left _), tsum_mul_left, tsum_ite_eq] using h

/-- Pointwise conjugation of the actual smooth function. -/
def conjugate : Test where
  lift x := conj (f.lift x)
  smooth := Complex.conjCLE.contDiff.comp f.smooth
  periodic x := congrArg conj (f.periodic x)

private theorem coefficient_conjugate (m : ℤ) :
    f.conjugate.coefficient m = conj (f.coefficient (-m)) := by
  rw [coefficient_circle, coefficient_circle, fourierCoeff,
    fourierCoeff, ← integral_conj]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  have hval : f.conjugate.periodic.lift x = conj (f.periodic.lift x) := by
    induction x using Quotient.inductionOn with
    | h x => simp only [Function.Periodic.lift_coe, conjugate]
  rw [hval, smul_eq_mul, smul_eq_mul, map_mul, neg_neg,
    ← fourier_neg]

end Test
end D5.S3.VertexAlgebra.Analysis.SmoothCircleFourier
