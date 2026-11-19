/- GID: D5/S3/Weil/ZetaPntBounds/MobiusDyadicUnitWeightParseval
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/MobiusDyadicUnitWeightParseval
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unconditional unit-weight Parseval for the literal signed dyadic Möbius difference. -/

import D5.S3.Arith.MoebiusLogarithmic.ReciprocalBound
import D5.S3.Weil.ZetaGamma.FormCore.LineFourier
import D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
import D5.S3.Weil.ZetaPntBounds.ZetaBoundsLower
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Order.Interval.Finset.SuccPred

/-! ## Unconditional unit-weight Parseval for the signed dyadic difference

The logarithmic change of variables and normalized Fourier phase below adapt the
sealed growth-admission proof of `fourier_mobiusLogProfile_one` to every positive
tilt. The Mellin identity itself is the original `initial_mellin_identity`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology ArithmeticFunction.Moebius
open scoped ENNReal InnerProductSpace FourierTransform

open D5.S3.Weil.ZetaGamma.FormCore.LineFourier
open D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
  (halfLineMeasure halfLineMellin initial_mellin_identity mobiusMellin mobiusPartialSum)

namespace D5.S3.Weil.ZetaPntBounds.MobiusDyadicUnitWeightParseval

section UnitWeightParseval

local notation "D" => (fun x : ℝ => mobiusPartialSum x - mobiusPartialSum (2 * x))

/-- The Mellin symbol of (S(x)-S(2x)), with the removable value at the origin. -/
def mobiusDyadicMellinSymbol (s : ℂ) : ℂ :=
  if s = 0 then (Real.log 2 : ℂ)
  else (1 - (2 : ℂ) ^ s) * ((riemannZeta (s + 1))⁻¹ - 1) / s

private theorem dyadic_two_cpow (s : ℂ) :
    (2 : ℂ) ^ s = Complex.exp ((Real.log 2 : ℂ) * s) := by
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    simpa only [Complex.ofReal_ofNat] using
      (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0), hlog]

private theorem mobiusDyadicMellinSymbol_continuousAt {s : ℂ} (hs : 0 ≤ s.re) :
    ContinuousAt mobiusDyadicMellinSymbol s := by
  let L : ℂ := (Real.log 2 : ℂ)
  let E : ℂ → ℂ := fun z => Complex.exp (L * z)
  let Z : ℂ → ℂ := fun z => riemannZeta₁ (z + 1)
  have hE (z : ℂ) : HasDerivAt E (Complex.exp (L * z) * L) z :=
    (hasDerivAt_const_mul L).cexp
  have hZ : Continuous Z := differentiable_riemannZeta₁.continuous.comp
    (continuous_id.add continuous_const)
  have hZn : Z s ≠ 0 := by
    rcases eq_or_ne s 0 with rfl | hn
    · simp [Z, riemannZeta₁_one]
    · have hs1 : s + 1 ≠ 1 := by simpa using hn
      have hζ : riemannZeta (s + 1) ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re (by simpa using hs)
      intro hz
      apply hζ
      rw [riemannZeta_eq_inv_sub_mul hs1]
      change ((s + 1) - 1)⁻¹ * Z s = 0
      rw [hz, mul_zero]
  have heq : mobiusDyadicMellinSymbol =
      fun z => dslope E 0 z * (1 - z * (Z z)⁻¹) := by
    funext z
    rcases eq_or_ne z 0 with rfl | hn
    · have hderiv : deriv E 0 = L := by simpa using (hE 0).deriv
      simp [mobiusDyadicMellinSymbol, dslope_same, hderiv, L]
    · have hz1 : z + 1 ≠ 1 := by simpa using hn
      have hζ : (riemannZeta (z + 1))⁻¹ = z * (Z z)⁻¹ := by
        simpa [Z] using inv_riemannZeta_eq_sub_mul_of_ne_one hz1
      rw [mobiusDyadicMellinSymbol, ite_eq_right hn, hζ, dslope_of_ne _ hn, slope_def_field,
        dyadic_two_cpow]
      simp only [E, L, mul_zero, Complex.exp_zero, sub_zero]
      ring
  rw [heq]
  have hS : ContinuousAt (dslope E 0) s := by
    rcases eq_or_ne s 0 with rfl | hn
    · exact continuousAt_dslope_same.mpr (hE 0).differentiableAt
    · exact (continuousAt_dslope_of_ne hn).2 (hE s).continuousAt
  have hI := hZ.continuousAt.inv₀ hZn
  exact hS.mul (continuousAt_const.sub (continuousAt_id.mul hI))

private theorem measurable_unitWeight_mobiusPartialSum : Measurable mobiusPartialSum :=
  (measurable_of_countable
    (fun k : ℕ => ∑ n ∈ Finset.Icc 1 k, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ))).comp
    Nat.measurable_floor

private theorem norm_mobiusPartialSum_exp_le {u : ℝ} (hu : 0 ≤ u) :
    ‖(mobiusPartialSum (Real.exp u) : ℂ)‖ ≤ 1 + u := by
  have hrange : Finset.Icc 1 ⌊Real.exp u⌋₊ = Finset.Ioc 0 ⌊Real.exp u⌋₊ :=
    Finset.Icc_succ_left_eq_Ioc (0 : ℕ) _
  rw [Complex.norm_real, Real.norm_eq_abs, mobiusPartialSum, hrange]
  change |D5.S3.Arith.MoebiusLogarithmic.reciprocalSum (Real.exp u)| ≤ 1 + u
  exact (D5.S3.Arith.MoebiusLogarithmic.abs_reciprocalSum_le_one (Real.exp u)).trans
    (by linarith)

private def unitWeightTilt (δ : ℝ) (g : ℝ → ℝ) : ℝ → ℂ :=
  (Ici 0).indicator (fun u => (Real.exp (-δ * u) : ℂ) * (g (Real.exp u) : ℂ))

private theorem measurable_unitWeightTilt (δ : ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (unitWeightTilt δ g) := by
  have he : Measurable (fun u : ℝ => (Real.exp (-δ * u) : ℂ)) := by fun_prop
  exact (he.mul (Complex.continuous_ofReal.measurable.comp
    (hg.comp Real.continuous_exp.measurable))).indicator measurableSet_Ici

private theorem norm_unitWeightTilt {δ : ℝ} {g : ℝ → ℝ} {u : ℝ} (hu : 0 ≤ u) :
    ‖unitWeightTilt δ g u‖ = Real.exp (-δ * u) * ‖(g (Real.exp u) : ℂ)‖ := by
  rw [unitWeightTilt, indicator_of_mem (show u ∈ Ici 0 from hu), norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]

private theorem integrable_unitWeightTilt {δ A : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A)
    {g : ℝ → ℝ} (hg : Measurable g)
    (hbound : ∀ u ≥ 0, ‖(g (Real.exp u) : ℂ)‖ ≤ A * (1 + u)) :
    Integrable (unitWeightTilt δ g) ∧ MemLp (unitWeightTilt δ g) 2 := by
  let B := A * (1 + 2 / δ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmeas : AEStronglyMeasurable (unitWeightTilt δ g) volume :=
    (measurable_unitWeightTilt δ hg).aestronglyMeasurable
  have hdecay (u : ℝ) (hu : 0 ≤ u) :
      ‖unitWeightTilt δ g u‖ ≤ B * Real.exp (-(δ / 2) * u) := by
    have he : 1 ≤ Real.exp (δ * u / 2) := by
      simpa using Real.exp_le_exp.mpr (show 0 ≤ δ * u / 2 by positivity)
    have hu' : u ≤ (2 / δ) * Real.exp (δ * u / 2) := by
      have hh : δ * u / 2 ≤ Real.exp (δ * u / 2) :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
      calc
        u = (2 / δ) * (δ * u / 2) := by field_simp <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)
    have hlin : 1 + u ≤ (1 + 2 / δ) * Real.exp (δ * u / 2) := by
      rw [add_mul, one_mul]
      exact add_le_add he hu'
    rw [norm_unitWeightTilt hu]
    calc
      _ ≤ Real.exp (-δ * u) * (A * (1 + u)) :=
        mul_le_mul_of_nonneg_left (hbound u hu) (Real.exp_nonneg _)
      _ ≤ Real.exp (-δ * u) * (A * ((1 + 2 / δ) * Real.exp (δ * u / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlin hA) (Real.exp_nonneg _)
      _ = B * Real.exp (-(δ / 2) * u) := by
        rw [show Real.exp (-(δ / 2) * u) =
          Real.exp (-δ * u) * Real.exp (δ * u / 2) by rw [← Real.exp_add]; congr 1 <;> ring]
        dsimp [B]
        ring
  have hEnvelope (b a : ℝ) (ha : a < 0) :
      Integrable ((Ici 0).indicator (fun u : ℝ => b * Real.exp (a * u))) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      ((integrableOn_exp_mul_Ioi ha 0).const_mul b)).integrable_indicator measurableSet_Ici
  constructor
  · refine (hEnvelope B (-(δ / 2)) (by linarith)).mono' hmeas ?_
    filter_upwards with u
    by_cases hu : 0 ≤ u
    · simpa only [indicator_of_mem (show u ∈ Ici 0 from hu)] using hdecay u hu
    · have hu' : u ∉ Ici (0 : ℝ) := hu
      simp [unitWeightTilt, hu']
  · apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
    refine (hEnvelope (B ^ 2) (-δ) (by linarith)).mono'
      (((measurable_unitWeightTilt δ hg).norm.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards with u
    by_cases hu : 0 ≤ u
    · rw [indicator_of_mem (show u ∈ Ici 0 from hu), Real.norm_of_nonneg (sq_nonneg _)]
      calc
        _ ≤ (B * Real.exp (-(δ / 2) * u)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hdecay u hu) 2
        _ = _ := by
          rw [mul_pow, ← Real.exp_nat_mul (-(δ / 2) * u) 2]
          congr 2 <;> ring
    · have hu' : u ∉ Ici (0 : ℝ) := hu
      simp [unitWeightTilt, hu']

private theorem exp_smul_unitWeightMellin (g : ℝ → ℝ) (s : ℂ) (u : ℝ) :
    Real.exp u • ((g (Real.exp u) : ℂ) * (Real.exp u : ℂ) ^ (-(s + 1))) =
      Complex.exp (-s * (u : ℂ)) * (g (Real.exp u) : ℂ) := by
  have hn : (Real.exp u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'
  rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log (Real.exp_nonneg u),
    Real.log_exp, Complex.real_smul, Complex.ofReal_exp]
  calc
    _ = (Complex.exp (u : ℂ) * Complex.exp ((u : ℂ) * -(s + 1))) *
        (g (Real.exp u) : ℂ) := by ring
    _ = _ := by
      rw [← Complex.exp_add, show (u : ℂ) + (u : ℂ) * -(s + 1) = -s * (u : ℂ) by ring]

private def unitWeightSection (δ ξ : ℝ) : ℂ :=
  (δ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I

private theorem unitWeightSection_re (δ ξ : ℝ) : (unitWeightSection δ ξ).re = δ := by
  simp [unitWeightSection, Complex.mul_re]

private theorem unitWeightSection_im (δ ξ : ℝ) :
    (unitWeightSection δ ξ).im = 2 * Real.pi * ξ := by
  simp [unitWeightSection, Complex.mul_im]

private theorem fourier_unitWeightTilt (δ ξ : ℝ) (g : ℝ → ℝ) :
    𝓕 (unitWeightTilt δ g) ξ = halfLineMellin (fun x => (g x : ℂ)) (unitWeightSection δ ξ) := by
  let s := unitWeightSection δ ξ
  have hphase (u : ℝ) :
      ((-2 * Real.pi * (u * ξ) : ℝ) : ℂ) * I + ((-δ * u : ℝ) : ℂ) = -s * (u : ℂ) := by
    dsimp [s, unitWeightSection]
    push_cast
    ring
  calc
    𝓕 (unitWeightTilt δ g) ξ =
        ∫ u : ℝ, (Ici (0 : ℝ)).indicator
          (fun v => Complex.exp (-s * (v : ℂ)) * (g (Real.exp v) : ℂ)) u := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards with u
      simp only [Real.inner_apply, smul_eq_mul]
      by_cases hu : u ∈ Ici (0 : ℝ)
      · simp only [unitWeightTilt, indicator_of_mem hu, Complex.ofReal_exp]
        rw [← mul_assoc, ← Complex.exp_add, hphase]
      · simp [unitWeightTilt, hu]
    _ = ∫ u : ℝ in Ioi 0, Real.exp u •
          ((g (Real.exp u) : ℂ) * (Real.exp u : ℂ) ^ (-(s + 1))) := by
      rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
      exact setIntegral_congr_fun measurableSet_Ioi
        (fun u _ => (exp_smul_unitWeightMellin g s u).symm)
    _ = _ := by
      simpa only [Real.exp_zero, halfLineMellin, halfLineMeasure] using
        (integral_comp_exp_Ioi (fun x : ℝ => (g x : ℂ) * (x : ℂ) ^ (-(s + 1))) 0)

private theorem integrableOn_unitWeightMellin {g : ℝ → ℝ} {s : ℂ}
    (hg : Measurable g) (h : Integrable (unitWeightTilt s.re g)) :
    IntegrableOn (fun x : ℝ => (g x : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  let f : ℝ → ℂ := fun x => (g x : ℂ) * (x : ℂ) ^ (-(s + 1))
  rw [← Real.exp_zero, ← integrableOn_comp_exp_Ioi f]
  have hm : AEStronglyMeasurable (fun u : ℝ => Real.exp u • f (Real.exp u))
      (volume.restrict (Ioi 0)) := by
    have hmeas : Measurable (fun u : ℝ => Complex.exp (-s * (u : ℂ)) *
        (g (Real.exp u) : ℂ)) :=
      (show Continuous (fun u : ℝ => Complex.exp (-s * (u : ℂ))) by fun_prop).measurable.mul
        (Complex.continuous_ofReal.measurable.comp (hg.comp Real.continuous_exp.measurable))
    simpa only [f, exp_smul_unitWeightMellin] using hmeas.aestronglyMeasurable
  apply (integrable_norm_iff hm).mp
  refine h.norm.integrableOn.congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
  change 0 < u at hu
  dsimp only [f]
  rw [norm_unitWeightTilt hu.le, exp_smul_unitWeightMellin, norm_mul, Complex.norm_exp]
  simp [Complex.mul_re]

private theorem mobiusPartialSum_eq_one_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 1 2) :
    mobiusPartialSum x = 1 := by
  have hfloor : ⌊x⌋₊ = 1 :=
    (Nat.floor_eq_iff (show 0 ≤ x by linarith [hx.1])).2
      ⟨by simpa using hx.1.le, by simpa [one_add_one_eq_two] using hx.2⟩
  rw [mobiusPartialSum, hfloor, Finset.Icc_self]
  simp

private theorem halfLineMellin_dyadic {s : ℂ} (hs : 0 < s.re) :
    halfLineMellin (fun x => (D x : ℂ)) s = mobiusDyadicMellinSymbol s := by
  have hn : s ≠ 0 := by intro h; simp [h] at hs
  let k : ℝ → ℂ := fun x => (x : ℂ) ^ (-(s + 1))
  let g : ℝ → ℂ := fun x => (mobiusPartialSum x : ℂ) * k x
  let f : ℝ → ℂ := fun x => ((mobiusPartialSum x : ℂ) - 1) * k x
  have hg : IntegrableOn g (Ioi 1) :=
    integrableOn_unitWeightMellin measurable_unitWeight_mobiusPartialSum
      (integrable_unitWeightTilt hs zero_le_one measurable_unitWeight_mobiusPartialSum
        (fun u hu => by simpa using norm_mobiusPartialSum_exp_le hu)).1
  have hneg : (-s).re < 0 := by simpa using hs
  have hkernel (u : ℝ) : Real.exp u • k (Real.exp u) = Complex.exp (-s * (u : ℂ)) := by
    simpa [k] using exp_smul_unitWeightMellin (fun _ => 1) s u
  have hk : IntegrableOn k (Ioi 1) := by
    rw [← Real.exp_zero, ← integrableOn_comp_exp_Ioi k]
    simpa only [hkernel] using integrableOn_exp_mul_complex_Ioi hneg 0
  have hkInt : (∫ x in Ioi (1 : ℝ), k x) = (1 : ℂ) / s := by
    rw [← Real.exp_zero, ← integral_comp_exp_Ioi k, integral_congr_ae (ae_of_all _ hkernel),
      integral_exp_mul_complex_Ioi hneg]
    simp
  have hfg (x : ℝ) : f x = g x - k x := by simp only [f, g, sub_mul, one_mul]
  have hf : IntegrableOn f (Ioi 1) := (hg.sub hk).congr (ae_of_all _ fun x => (hfg x).symm)
  have hIntg : (∫ x in Ioi (1 : ℝ), g x) = (riemannZeta (s + 1))⁻¹ / s := by
    change mobiusMellin s = _
    apply (eq_div_iff hn).2
    simpa only [one_div, mul_comm (mobiusMellin s) s] using initial_mellin_identity hs
  have hIntf : (∫ x in Ioi (1 : ℝ), f x) = ((riemannZeta (s + 1))⁻¹ - 1) / s := by
    simp_rw [hfg]
    rw [integral_sub hg hk, hIntg, hkInt, sub_div]
  have htail : (∫ x in Ioi (1 : ℝ), f x) = ∫ x in Ioi (2 : ℝ), f x := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
      (Ioi_subset_Ioi (by norm_num)) ?_
    filter_upwards [volume.ae_ne (2 : ℝ)] with x hx hx'
    have hx₁ : 1 < x := hx'.1
    have hx₂ : x ≤ 2 := le_of_not_gt hx'.2
    dsimp only [f]
    rw [mobiusPartialSum_eq_one_of_mem_Ioo ⟨hx₁, lt_of_le_of_ne hx₂ hx⟩]
    simp
  let C : ℂ := (2 : ℂ) ^ (s + 1)
  have hC : C ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hscale (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      ((mobiusPartialSum (2 * x) : ℂ) - 1) * k x = C * f (2 * x) := by
    have hx₀ : 0 ≤ x := zero_le_one.trans (le_of_lt hx)
    dsimp only [f, k]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hx₀,
      Complex.ofReal_ofNat, Complex.cpow_neg (2 : ℂ)]
    calc
      _ = (C * C⁻¹) * (((mobiusPartialSum (2 * x) : ℂ) - 1) * (x : ℂ) ^ (-(s + 1))) := by
        rw [mul_inv_cancel₀ hC, one_mul]
      _ = _ := by ring
  have hfComp : IntegrableOn (fun x : ℝ => C * f (2 * x)) (Ioi 1) := by
    apply Integrable.const_mul
    exact (integrableOn_Ioi_comp_mul_left_iff f 1 (by norm_num : 0 < (2 : ℝ))).2
      (hf.mono_set (Ioi_subset_Ioi (by norm_num)))
  have hsplit : halfLineMellin (fun x => (D x : ℂ)) s =
      (∫ x in Ioi (1 : ℝ), f x) - ∫ x in Ioi (1 : ℝ), C * f (2 * x) := by
    rw [← integral_sub hf hfComp]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [← hscale x hx]
    change (↑(D x) : ℂ) * k x = f x - _
    push_cast
    simp only [f]
    ring
  have hscaleInt : (∫ x in Ioi (1 : ℝ), C * f (2 * x)) =
      (2 : ℂ) ^ s * (∫ x in Ioi (1 : ℝ), f x) := by
    rw [integral_const_mul, integral_comp_mul_left_Ioi f 1 (by norm_num : 0 < (2 : ℝ)),
      mul_one, ← htail, Complex.real_smul]
    have htwo : (2 : ℂ) ≠ 0 := by norm_num
    rw [show C = (2 : ℂ) ^ s * 2 by
      dsimp only [C]
      rw [Complex.cpow_add s 1 htwo, Complex.cpow_one]]
    simp only [Complex.ofReal_inv, Complex.ofReal_ofNat]
    rw [mul_assoc ((2 : ℂ) ^ s), ← mul_assoc (2 : ℂ), mul_inv_cancel₀ htwo, one_mul]
  rw [hsplit, hscaleInt, hIntf, mobiusDyadicMellinSymbol, ite_eq_right hn]
  ring

private theorem zeta_inv_norm_le_log_seven :
    ∃ K > 0, ∀ σ ∈ Icc (1 : ℝ) 2, ∀ t : ℝ, 3 < |t| →
      1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K * (Real.log |t|) ^ (7 : ℝ) := by
  obtain ⟨A, hA, K₁, hK₁, hnear⟩ := ZetaInvBnd
  obtain ⟨K₂, hK₂, hfar⟩ := ZetaInvBound2
  let K := max K₁ (K₂ * A ^ (-(3 : ℝ) / 4))
  refine ⟨K, hK₁.trans_le (le_max_left _ _), ?_⟩
  intro σ hσ t ht
  let L := Real.log |t|
  have hL : 0 < L := Real.log_pos (by linarith)
  let w := A / L ^ (9 : ℕ)
  have hw : 0 < w := div_pos hA.1 (pow_pos hL _)
  by_cases hσnear : σ < 1 + w
  · exact (hnear σ t ht ⟨(sub_le_self _ hw.le).trans hσ.1, hσnear⟩).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hL.le _))
  · have hwσ : w ≤ σ - 1 := by linarith [le_of_not_gt hσnear]
    have hσgt : 1 < σ := by linarith
    calc
      _ ≤ K₂ * (σ - 1) ^ (-(3 : ℝ) / 4) * L ^ (1 / 4 : ℝ) :=
        hfar ⟨hσgt, hσ.2⟩ t ht
      _ ≤ K₂ * w ^ (-(3 : ℝ) / 4) * L ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hw hwσ (by norm_num)) hK₂.le) (Real.rpow_nonneg hL.le _)
      _ = (K₂ * A ^ (-(3 : ℝ) / 4)) * L ^ (7 : ℝ) := by
        dsimp only [w]
        rw [Real.div_rpow hA.1.le (pow_nonneg hL.le _) _,
          ← Real.rpow_natCast_mul hL.le 9 (-(3 : ℝ) / 4),
          show ((9 : ℕ) : ℝ) * (-(3 : ℝ) / 4) = -(27 / 4 : ℝ) by norm_num,
          Real.rpow_neg hL.le, div_inv_eq_mul, ← mul_assoc K₂,
          mul_assoc (K₂ * A ^ (-(3 : ℝ) / 4)), ← Real.rpow_add hL]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hL.le _)

private theorem norm_mobiusDyadicMellinSymbol_le_on_strip :
    ∃ C > 0, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 →
      ‖mobiusDyadicMellinSymbol s‖ ≤ C * (1 + |s.im|) ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨K, hK, hInv⟩ := zeta_inv_norm_le_log_seven
  have hlarge : ∀ᶠ y : ℝ in atTop, 3 < y ∧
      Real.log y ^ (7 : ℝ) ≤ y ^ (1 / 4 : ℝ) := by
    filter_upwards [eventually_gt_atTop (3 : ℝ),
      (isLittleO_log_rpow_rpow_atTop (7 : ℝ) (by norm_num : 0 < (1 / 4 : ℝ))).eventuallyLE]
      with y hy hlog
    have hy₀ : 0 ≤ y := by linarith
    have hlog₀ : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog₀ _),
      Real.norm_of_nonneg (Real.rpow_nonneg hy₀ _)] at hlog
    exact ⟨hy, hlog⟩
  obtain ⟨T, hT⟩ := eventually_atTop.1 hlarge
  have hT₁ : 0 < 1 + T := by linarith [(hT T le_rfl).1]
  let R : Set ℂ := Icc 0 1 ×ℂ Icc (-T) T
  have hR : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B, hB⟩ := hR.exists_bound_of_continuousOn
    (show ContinuousOn mobiusDyadicMellinSymbol R from fun _ hs =>
      (mobiusDyadicMellinSymbol_continuousAt hs.1.1).continuousWithinAt)
  let C := max (6 * (K + 1)) (max B 0 * (1 + T) ^ (3 / 4 : ℝ))
  have hC : 0 < C := (show 0 < 6 * (K + 1) by positivity).trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro s hs₀ hs₁
  have hb : 0 < 1 + |s.im| := by positivity
  have hp := Real.rpow_nonneg hb.le (-(3 / 4 : ℝ))
  by_cases ht : T ≤ |s.im|
  · obtain ⟨ht₃, hlog⟩ := hT _ ht
    have him := Complex.abs_im_le_norm s
    have hnorm : 0 < ‖s‖ := by linarith
    have hre : (s + 1).re ∈ Icc (1 : ℝ) 2 := by
      change 1 ≤ (s + 1).re ∧ (s + 1).re ≤ 2
      rw [Complex.add_re, Complex.one_re]
      constructor <;> linarith
    have hi : (s + 1).im = s.im := by simp
    have hz := hInv (s + 1).re hre (s + 1).im (by rwa [hi])
    rw [Complex.re_add_im, hi] at hz
    have hpow : ‖(2 : ℂ) ^ s‖ ≤ 2 := by
      change ‖((2 : ℝ) : ℂ) ^ s‖ ≤ 2
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : 0 < (2 : ℝ))]
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs₁
    have hfac : ‖1 - (2 : ℂ) ^ s‖ ≤ 3 := by
      have h := norm_sub_le (1 : ℂ) ((2 : ℂ) ^ s)
      rw [norm_one] at h
      linarith
    have h1 : 1 ≤ Real.log |s.im| ^ (7 : ℝ) :=
      Real.one_le_rpow (logt_gt_one ht₃.le).le (by norm_num)
    have hrec : ‖(riemannZeta (s + 1))⁻¹ - 1‖ ≤
        (K + 1) * Real.log |s.im| ^ (7 : ℝ) := by
      calc
        _ ≤ 1 / ‖riemannZeta (s + 1)‖ + 1 := by
          simpa [norm_inv, one_div] using norm_sub_le (riemannZeta (s + 1))⁻¹ (1 : ℂ)
        _ ≤ _ := by rw [add_mul, one_mul]; exact add_le_add hz h1
    have hquarter : |s.im| ^ (1 / 4 : ℝ) ≤ (1 + |s.im|) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by norm_num)
    rw [mobiusDyadicMellinSymbol, ite_eq_right (norm_pos_iff.mp hnorm), norm_div, norm_mul]
    apply (div_le_iff₀ hnorm).2
    calc
      _ ≤ 3 * ((K + 1) * Real.log |s.im| ^ (7 : ℝ)) :=
        mul_le_mul hfac hrec (norm_nonneg _) (by norm_num)
      _ ≤ 3 * ((K + 1) * (1 + |s.im|) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hlog.trans hquarter) (by positivity)) (by norm_num)
      _ = 3 * (K + 1) * (1 + |s.im|) * (1 + |s.im|) ^ (-(3 / 4 : ℝ)) := by
        rw [show (1 / 4 : ℝ) = 1 + -(3 / 4 : ℝ) by norm_num,
          Real.rpow_add hb, Real.rpow_one]
        ring
      _ ≤ 3 * (K + 1) * (2 * ‖s‖) * (1 + |s.im|) ^ (-(3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hp
      _ = (6 * (K + 1)) * (1 + |s.im|) ^ (-(3 / 4 : ℝ)) * ‖s‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hp) hnorm.le
  · have hsR : s ∈ R := ⟨⟨hs₀, hs₁⟩, abs_le.mp (le_of_not_ge ht)⟩
    have hpow : (1 + T) ^ (-(3 / 4 : ℝ)) ≤ (1 + |s.im|) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hb (add_le_add_right (le_of_not_ge ht) 1) (by norm_num)
    calc
      ‖mobiusDyadicMellinSymbol s‖ ≤ B := hB s hsR
      _ ≤ max B 0 := le_max_left _ _
      _ = (max B 0 * (1 + T) ^ (3 / 4 : ℝ)) * (1 + T) ^ (-(3 / 4 : ℝ)) := by
        rw [mul_assoc, ← Real.rpow_add hT₁, add_neg_cancel, Real.rpow_zero, mul_one]
      _ ≤ _ := mul_le_mul (le_max_right _ _) hpow (Real.rpow_nonneg hT₁.le _) hC.le

private def unitWeightMass (f : ℝ → ℂ) (u : ℝ) : ℝ≥0∞ := ENNReal.ofReal (‖f u‖ ^ 2)

private theorem lintegral_unitWeightMass_eq_eLpNorm (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume) :
    (∫⁻ u : ℝ, unitWeightMass f u) = eLpNorm f 2 volume ^ 2 := by
  have h (u : ℝ) : unitWeightMass f u = ‖f u‖ₑ ^ 2 := by
    rw [unitWeightMass, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [show (∫⁻ u : ℝ, unitWeightMass f u) = ∫⁻ u : ℝ, ‖f u‖ₑ ^ 2 from lintegral_congr h]
  exact squared_mass_eq_eLpNorm f hf

private def unitWeightDelta (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private theorem unitWeightDelta_pos (n : ℕ) : 0 < unitWeightDelta n := by
  unfold unitWeightDelta
  positivity

private theorem unitWeightDelta_le_one (n : ℕ) : unitWeightDelta n ≤ 1 := by
  simpa only [unitWeightDelta, div_one] using
    one_div_le_one_div_of_le zero_lt_one
      (show (1 : ℝ) ≤ (n : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) n])

private theorem unitWeightDelta_antitone : Antitone unitWeightDelta := by
  intro n m hnm
  exact one_div_le_one_div_of_le (by positivity)
    (add_le_add_left (Nat.cast_le.mpr hnm) 1)

private theorem unitWeightDelta_tendsto : Tendsto unitWeightDelta atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private theorem measurable_unitWeight_difference : Measurable D :=
  measurable_unitWeight_mobiusPartialSum.sub
    (measurable_unitWeight_mobiusPartialSum.comp (by fun_prop))

private theorem norm_unitWeight_difference_exp_le {u : ℝ} (hu : 0 ≤ u) :
    ‖(D (Real.exp u) : ℂ)‖ ≤ (2 + Real.log 2) * (1 + u) := by
  have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he : Real.exp (Real.log 2 + u) = 2 * Real.exp u := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  change ‖((mobiusPartialSum (Real.exp u) - mobiusPartialSum (2 * Real.exp u) : ℝ) : ℂ)‖ ≤ _
  rw [Complex.ofReal_sub, ← he]
  calc
    _ ≤ ‖(mobiusPartialSum (Real.exp u) : ℂ)‖ +
        ‖(mobiusPartialSum (Real.exp (Real.log 2 + u)) : ℂ)‖ := norm_sub_le _ _
    _ ≤ (1 + u) + (1 + (Real.log 2 + u)) :=
      add_le_add (norm_mobiusPartialSum_exp_le hu)
        (norm_mobiusPartialSum_exp_le (add_nonneg hL hu))
    _ ≤ _ := by nlinarith [mul_nonneg hL hu]

private theorem continuous_unitWeightSection_symbol {δ : ℝ} (hδ : 0 ≤ δ) :
    Continuous (fun ξ => mobiusDyadicMellinSymbol (unitWeightSection δ ξ)) := by
  apply continuous_iff_continuousAt.mpr
  intro ξ
  exact (mobiusDyadicMellinSymbol_continuousAt (by rwa [unitWeightSection_re])).comp
    (show ContinuousAt (unitWeightSection δ) ξ by unfold unitWeightSection; fun_prop)

private theorem unitWeightSection_symbol_tendsto (ξ : ℝ) :
    Tendsto (fun n => mobiusDyadicMellinSymbol (unitWeightSection (unitWeightDelta n) ξ))
      atTop (𝓝 (mobiusDyadicMellinSymbol (unitWeightSection 0 ξ))) := by
  have h : ContinuousAt (fun δ => unitWeightSection δ ξ) 0 := by
    unfold unitWeightSection
    fun_prop
  exact (mobiusDyadicMellinSymbol_continuousAt (s := unitWeightSection 0 ξ)
    (by simp only [unitWeightSection_re, le_refl])).tendsto.comp
    (h.tendsto.comp unitWeightDelta_tendsto)

private theorem unitWeight_mass_tendsto_time (u : ℝ) :
    Tendsto (fun n => unitWeightMass (unitWeightTilt (unitWeightDelta n) D) u) atTop
      (𝓝 (unitWeightMass (unitWeightTilt 0 D) u)) := by
  have h : ContinuousAt (fun δ => unitWeightMass (unitWeightTilt δ D) u) 0 := by
    by_cases hu : u ∈ Ici (0 : ℝ)
    · simp only [unitWeightMass, unitWeightTilt, indicator_of_mem hu]
      apply ENNReal.continuous_ofReal.continuousAt.comp
      fun_prop
    · simp [unitWeightMass, unitWeightTilt, hu, continuousAt_const]
  exact h.tendsto.comp unitWeightDelta_tendsto

private theorem unitWeight_mass_monotone_time (u : ℝ) :
    Monotone (fun n => unitWeightMass (unitWeightTilt (unitWeightDelta n) D) u) := by
  intro n m hnm
  by_cases hu : 0 ≤ u
  · simp only [unitWeightMass, norm_unitWeightTilt hu]
    apply ENNReal.ofReal_le_ofReal
    have hexp : Real.exp (-unitWeightDelta n * u) ≤ Real.exp (-unitWeightDelta m * u) :=
      Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (neg_le_neg (unitWeightDelta_antitone hnm)) hu)
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right hexp (norm_nonneg _)) 2
  · have hu' : u ∉ Ici (0 : ℝ) := hu
    simp [unitWeightMass, unitWeightTilt, hu']

/-- The critical energy of the literal signed Möbius difference is finite and
satisfies Parseval, with frequency measured in the normalized Fourier variable. -/
theorem mobiusDyadicDifference_unitWeight_parseval :
    IntegrableOn
      (fun x : ℝ => (mobiusPartialSum x - mobiusPartialSum (2 * x)) ^ 2 * x⁻¹) (Ioi 1) ∧
    Integrable (fun ξ : ℝ =>
      ‖mobiusDyadicMellinSymbol (((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2) ∧
    (∫ x in Ioi (1 : ℝ), (mobiusPartialSum x - mobiusPartialSum (2 * x)) ^ 2 * x⁻¹) =
      ∫ ξ : ℝ, ‖mobiusDyadicMellinSymbol (((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2 := by
  let f : ℝ → ℝ → ℂ := fun δ => unitWeightTilt δ D
  let F : ℝ → ℝ → ℂ := fun δ ξ => mobiusDyadicMellinSymbol (unitWeightSection δ ξ)
  have hfMeas (δ : ℝ) : Measurable (f δ) :=
    measurable_unitWeightTilt δ measurable_unitWeight_difference
  have hFCont (δ : ℝ) (hδ : 0 ≤ δ) : Continuous (F δ) :=
    continuous_unitWeightSection_symbol hδ
  have hline (n : ℕ) : (∫⁻ u : ℝ, unitWeightMass (f (unitWeightDelta n)) u) =
      ∫⁻ ξ : ℝ, unitWeightMass (F (unitWeightDelta n)) ξ := by
    let δ := unitWeightDelta n
    have hδ : 0 < δ := unitWeightDelta_pos n
    obtain ⟨hf₁, hf₂⟩ := integrable_unitWeightTilt hδ
      (show 0 ≤ 2 + Real.log 2 by
        linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
      measurable_unitWeight_difference (fun _ hu => norm_unitWeight_difference_exp_le hu)
    have hFourier : 𝓕 (f δ) = F δ := by
      funext ξ
      exact (fourier_unitWeightTilt δ ξ D).trans
        (halfLineMellin_dyadic (by rwa [unitWeightSection_re]))
    rw [lintegral_unitWeightMass_eq_eLpNorm _ hf₂.aestronglyMeasurable,
      lintegral_unitWeightMass_eq_eLpNorm _ (hFCont δ hδ.le).aestronglyMeasurable,
      ← hFourier, raw_fourier_eLpNorm_eq hf₁ hf₂]
  obtain ⟨C, hC, hstrip⟩ := norm_mobiusDyadicMellinSymbol_le_on_strip
  let M : ℝ → ℝ := fun ξ => C ^ 2 * (1 + ‖2 * Real.pi * ξ‖) ^ (-(3 / 2 : ℝ))
  have hM : Integrable M := by
    have hbase : Integrable (fun ξ : ℝ => (1 + ‖ξ‖) ^ (-(3 / 2 : ℝ))) :=
      integrable_one_add_norm (by norm_num)
    have h := hbase.comp_mul_left' (show 2 * Real.pi ≠ 0 by positivity)
    simpa only [M, mul_assoc] using h.const_mul (C ^ 2)
  have hM₀ (ξ : ℝ) : 0 ≤ M ξ := by
    dsimp [M]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hMfin : (∫⁻ ξ : ℝ, ENNReal.ofReal (M ξ)) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hM.aestronglyMeasurable (ae_of_all _ hM₀)).2 hM
  have hdom (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (ξ : ℝ) :
      unitWeightMass (F δ) ξ ≤ ENNReal.ofReal (M ξ) := by
    have h := hstrip (unitWeightSection δ ξ)
      (by rwa [unitWeightSection_re]) (by rwa [unitWeightSection_re])
    rw [unitWeightSection_im, ← Real.norm_eq_abs] at h
    apply ENNReal.ofReal_le_ofReal
    calc
      ‖F δ ξ‖ ^ 2 ≤ (C * (1 + ‖2 * Real.pi * ξ‖) ^ (-(3 / 4 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = M ξ := by
        simp only [M, Real.norm_eq_abs, mul_pow]
        rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ 1 + |2 * Real.pi * ξ|)]
        norm_num
  have hmeasMass {g : ℝ → ℂ} (hg : Measurable g) :
      AEMeasurable (unitWeightMass g) volume :=
    (hg.norm.pow_const 2).aemeasurable.ennreal_ofReal
  have htime : Tendsto (fun n => ∫⁻ u : ℝ, unitWeightMass (f (unitWeightDelta n)) u) atTop
      (𝓝 (∫⁻ u : ℝ, unitWeightMass (f 0) u)) :=
    lintegral_tendsto_of_tendsto_of_monotone
      (fun n => hmeasMass (hfMeas (unitWeightDelta n)))
      (ae_of_all _ unitWeight_mass_monotone_time)
      (ae_of_all _ unitWeight_mass_tendsto_time)
  have hfreq : Tendsto (fun n => ∫⁻ ξ : ℝ, unitWeightMass (F (unitWeightDelta n)) ξ) atTop
      (𝓝 (∫⁻ ξ : ℝ, unitWeightMass (F 0) ξ)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun ξ => ENNReal.ofReal (M ξ))
      (fun n => hmeasMass (hFCont _ (unitWeightDelta_pos n).le).measurable)
      (fun n => ae_of_all _ (hdom _ (unitWeightDelta_pos n).le (unitWeightDelta_le_one n)))
      hMfin (ae_of_all _ fun ξ => ?_)
    have hc : Continuous (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)) :=
      ENNReal.continuous_ofReal.comp (continuous_norm.pow 2)
    exact (hc.continuousAt.tendsto.comp (unitWeightSection_symbol_tendsto ξ))
  have hext : (∫⁻ u : ℝ, unitWeightMass (f 0) u) = ∫⁻ ξ : ℝ, unitWeightMass (F 0) ξ :=
    tendsto_nhds_unique htime (hfreq.congr' (Eventually.of_forall fun n => (hline n).symm))
  have hfreqFin : (∫⁻ ξ : ℝ, unitWeightMass (F 0) ξ) ≠ ∞ :=
    ne_of_lt ((lintegral_mono (hdom 0 le_rfl zero_le_one)).trans_lt (lt_top_iff_ne_top.mpr hMfin))
  have htimeFin : (∫⁻ u : ℝ, unitWeightMass (f 0) u) ≠ ∞ := by
    rw [hext]
    exact hfreqFin
  have htimeSq : Integrable (fun u : ℝ => ‖f 0 u‖ ^ 2) :=
    (lintegral_ofReal_ne_top_iff_integrable ((hfMeas 0).norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun _ => sq_nonneg _)).1 htimeFin
  have hfreqSq : Integrable (fun ξ : ℝ => ‖F 0 ξ‖ ^ 2) :=
    (lintegral_ofReal_ne_top_iff_integrable ((hFCont 0 le_rfl).norm.pow 2).aestronglyMeasurable
      (ae_of_all _ fun _ => sq_nonneg _)).1 hfreqFin
  have hreal : (∫ u : ℝ, ‖f 0 u‖ ^ 2) = ∫ ξ : ℝ, ‖F 0 ξ‖ ^ 2 := by
    have hnn (g : ℝ → ℂ) : 0 ≤ᵐ[(volume : Measure ℝ)] (fun u => ‖g u‖ ^ 2) :=
      ae_of_all _ fun _ => sq_nonneg _
    unfold unitWeightMass at hext
    rw [← ofReal_integral_eq_lintegral_ofReal htimeSq (hnn (f 0)),
      ← ofReal_integral_eq_lintegral_ofReal hfreqSq (hnn (F 0))] at hext
    exact (ENNReal.ofReal_eq_ofReal_iff
      (integral_nonneg (fun _ => sq_nonneg _)) (integral_nonneg (fun _ => sq_nonneg _))).1 hext
  let energy : ℝ → ℝ := fun x => D x ^ 2 * x⁻¹
  have hchange (u : ℝ) (hu : 0 ≤ u) : ‖f 0 u‖ ^ 2 = Real.exp u • energy (Real.exp u) := by
    dsimp only [f, energy]
    rw [norm_unitWeightTilt hu, Complex.norm_real, Real.norm_eq_abs, neg_zero, zero_mul,
      Real.exp_zero, one_mul, sq_abs, smul_eq_mul]
    have he := Real.exp_ne_zero u
    calc
      _ = (Real.exp u * (Real.exp u)⁻¹) * D (Real.exp u) ^ 2 := by
        rw [mul_inv_cancel₀ he, one_mul]
      _ = _ := by ring
  have hOn : IntegrableOn (fun u : ℝ => Real.exp u • energy (Real.exp u)) (Ioi 0) := by
    refine htimeSq.integrableOn.congr ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
    exact hchange u (le_of_lt hu)
  have hEnergy : IntegrableOn energy (Ioi 1) := by
    simpa only [Real.exp_zero] using (integrableOn_comp_exp_Ioi energy 0).1 hOn
  have hTimeEnergy : (∫ u : ℝ, ‖f 0 u‖ ^ 2) = ∫ x in Ioi (1 : ℝ), energy x := by
    calc
      _ = ∫ u : ℝ, (Ici (0 : ℝ)).indicator (fun v => Real.exp v • energy (Real.exp v)) u := by
        apply integral_congr_ae
        filter_upwards with u
        by_cases hu : u ∈ Ici (0 : ℝ)
        · rw [indicator_of_mem hu, hchange u hu]
        · simp [f, unitWeightTilt, hu]
      _ = ∫ u in Ioi (0 : ℝ), Real.exp u • energy (Real.exp u) := by
        rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
      _ = _ := by simpa only [Real.exp_zero] using integral_comp_exp_Ioi energy 0
  refine ⟨hEnergy, ?_, ?_⟩
  · simpa only [F, unitWeightSection, Complex.ofReal_zero, zero_add] using hfreqSq
  · simpa only [energy, F, unitWeightSection, Complex.ofReal_zero, zero_add] using
      hTimeEnergy.symm.trans hreal

end UnitWeightParseval

end D5.S3.Weil.ZetaPntBounds.MobiusDyadicUnitWeightParseval
