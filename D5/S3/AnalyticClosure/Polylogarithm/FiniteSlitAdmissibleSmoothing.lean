/- GID: D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitAdmissibleSmoothing
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/FiniteSlitAdmissibleSmoothing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original admissible ordinary coefficients at every fixed positive smoothing order. -/

import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinarySmoothing
import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitRadialMargin

/-! The original admissible source discharges the radial and Abel smoothing inputs. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Filter Set Topology
open scoped BigOperators
namespace D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitAdmissibleSmoothing
open FiniteSlitOrdinarySmoothing

private theorem first (p : PowerSeries ℝ) (L : ℝ) (n : ℕ) :
    smooth (p - PowerSeries.C L) 1 n =
      (∑ i ∈ Finset.range (n+1), PowerSeries.coeff i p) - L := by
  have hfirst : smooth p 1 n = ∑ i ∈ Finset.range (n+1), PowerSeries.coeff i p := by
    rw [smooth, mul_comm, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  rw [smooth, mul_sub, map_sub, PowerSeries.coeff_mul_C]
  change smooth p 1 n - _ = _
  rw [hfirst]
  simp [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]

private theorem first_series (head : ℕ+) (tail : List ℕ+) (ell : ℕ+)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    HasSum (fun n ↦ smooth (FiniteSlitOrdinaryCoefficients.ordinary head tail ell -
      PowerSeries.C (FiniteSlitOrdinaryEndpoint.endpoint head tail ell)) 1 n * r ^ n)
      (((FiniteSlitCompositionMoments.reciprocal head tail ell (r : ℂ)).re -
        FiniteSlitOrdinaryEndpoint.endpoint head tail ell) / (1-r)) := by
  let p := FiniteSlitOrdinaryCoefficients.ordinary head tail ell
  let L := FiniteSlitOrdinaryEndpoint.endpoint head tail ell
  have hrc : ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hr1
  have ha : HasSum (fun n ↦ PowerSeries.coeff n p * r ^ n)
      (FiniteSlitCompositionMoments.reciprocal head tail ell (r : ℂ)).re := by
    have h := Complex.reCLM.hasSum
      ((FiniteSlitOrdinaryCoefficients.result head tail ell).2.1 (r : ℂ) hrc)
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, ← Complex.ofReal_pow, mul_zero, sub_zero, p] using h
  have hg : HasSum (fun n : ℕ ↦ r ^ n) ((1-r)⁻¹) :=
    hasSum_geometric_of_abs_lt_one (by rwa [abs_of_pos hr])
  have hc := hasSum_sum_range_mul_of_summable_norm ha.summable.norm hg.summable.norm
  rw [ha.tsum_eq, hg.tsum_eq] at hc
  have hprod (n : ℕ) : (∑ i ∈ Finset.range (n+1),
      (PowerSeries.coeff i p * r ^ i) * r ^ (n-i)) =
      (∑ i ∈ Finset.range (n+1), PowerSeries.coeff i p) * r ^ n := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le (by simpa using Finset.mem_range.mp hi)]
  have hh := hc.sub (hg.mul_left L)
  convert hh using 1
  · funext n
    rw [first, hprod]
    ring
  · dsimp [L]
    ring

/-- Every admissible positive composition has the original eventual negative
zeroth coefficients and every fixed positive smoothing order has the strict
zeta/binomial excess. No head-one conclusion is included. -/
theorem result (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) (hh : 1 < (head : ℕ)) :
    (∀ᶠ n : ℕ in atTop,
      PowerSeries.coeff n (FiniteSlitOrdinaryCoefficients.ordinary head tail ell) < 0) ∧
    ∀ j : ℕ, 1 ≤ j → ∀ᶠ n : ℕ in atTop,
      0 < smooth (FiniteSlitOrdinaryCoefficients.ordinary head tail ell) j n ∧
      (CompositionBoundary.zeta head tail)⁻¹ ^ (ell : ℕ) *
        (Nat.choose (n+j-1) n : ℝ) <
          smooth (FiniteSlitOrdinaryCoefficients.ordinary head tail ell) j n := by
  let p := FiniteSlitOrdinaryCoefficients.ordinary head tail ell
  let L := FiniteSlitOrdinaryEndpoint.endpoint head tail ell
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < smooth (p - PowerSeries.C L) 1 n := by
    filter_upwards [(FiniteSlitOrdinaryEndpoint.result head tail ell).2.2] with n hn
    rw [first]
    exact sub_pos.mpr hn
  have hall := FiniteSlitOrdinarySmoothing.result p L
    (fun r ↦ ((FiniteSlitCompositionMoments.reciprocal head tail ell (r : ℂ)).re - L)/(1-r))
    hpos (first_series head tail ell) (FiniteSlitRadialMargin.result head tail ell hh)
  refine ⟨(FiniteSlitOrdinaryCoefficients.result head tail ell).2.2, ?_⟩
  intro j hj
  filter_upwards [hall j hj] with n hn
  have hL : L = (CompositionBoundary.zeta head tail)⁻¹ ^ (ell : ℕ) := by
    simp only [L, FiniteSlitOrdinaryEndpoint.endpoint, if_pos hh]
  rw [hL] at hn
  refine ⟨?_, hn⟩
  exact lt_of_le_of_lt (mul_nonneg (pow_nonneg
    (inv_nonneg.mpr (CompositionBoundary.result head tail hh).2.2.2.1.le) _)
      (Nat.cast_nonneg _)) hn

end D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitAdmissibleSmoothing
