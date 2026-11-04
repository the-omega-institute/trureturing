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


private theorem leading_one_margin (tail : List ℕ+) (ell : ℕ+) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in 𝓝[<] 1,
      c ≤ ((FiniteSlitCompositionMoments.reciprocal 1 tail ell (r : ℂ)).re -
        FiniteSlitOrdinaryEndpoint.endpoint 1 tail ell) / (1-r) := by
  have hcases := CompositionBanksSourceInduction.composition_remainder_cases_of_controls 1 tail
    CompositionBanksLeadingClosure.composition_continued_norm_bound
    CompositionBanksOrdinaryTransport.ordinary_admissible_remainder_step
    CompositionBanksLeadingClosure.leading_one_remainder_iterate
    CompositionBanksLeadingTransport.split_leading_ones
  rcases hcases with hbad | ⟨q, suffix, _hhead, _hq, hlist, _hsuffix, hremainder⟩
  · norm_num at hbad
  · obtain ⟨ρ, D, N, hρ, _hρ1, hD, hbound⟩ :=
      CompositionBanksLeadingClosure.leading_one_continued_norm_bound_of_remainder
        CompositionBanksSourceInduction.leadingOneRemainder (by
          intro k rest hk
          rcases hk with ⟨_hs, η, C, M, P, hη, hη1, hC, hd, _hc, he⟩
          exact ⟨η, C, M, P, hη, hη1, hC, hd, he⟩) q suffix hremainder
    have hbound' : ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
        ‖CompositionContinuation.continued ((1 : ℕ+) :: tail) (1-w)‖ ≤
          D * (1 + ‖-Complex.log w‖)^N := by
      simpa only [← hlist] using hbound
    have hw : Tendsto (fun r : ℝ ↦ (1 : ℂ) - (r : ℂ)) (𝓝[<] 1)
        (𝓝[Complex.slitPlane] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · have ht : Tendsto (fun r : ℝ ↦ (r : ℂ)) (𝓝[<] 1) (𝓝 (1 : ℂ)) := by
          simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
        simpa using (tendsto_const_nhds (x := (1 : ℂ))).sub ht
      · filter_upwards [self_mem_nhdsWithin] with r hr
        rw [Complex.mem_slitPlane_iff]
        left
        simpa using sub_pos.mpr (show r < 1 from hr)
    have hwnorm : Tendsto (fun r : ℝ ↦ ‖(1 : ℂ) - (r : ℂ)‖)
        (𝓝[<] 1) (𝓝 (0 : ℝ)) := by simpa using (hw.mono_right nhdsWithin_le_nhds).norm
    have hdecay := (CompositionBanksLeadingClosure.slit_remainder_majorant_tendsto_zero
      (D ^ (ell : ℕ)) (N * (ell : ℕ)) (pow_nonneg hD _)).comp hw
    have hnum : Tendsto (fun r : ℝ ↦ r ^ (CompositionDisk.depth tail * (ell : ℕ)))
        (𝓝[<] 1) (𝓝 1) := by
      simpa using (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun r : ℝ ↦ r) (𝓝[<] 1) (𝓝 1)).pow
          (CompositionDisk.depth tail * (ell : ℕ))
    refine ⟨1, zero_lt_one, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num),
      hnum.eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ) < 1)),
      hdecay.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2)),
      (hwnorm.eventually (Iio_mem_nhds hρ))] with r hr hn hd hsmall
    have hrc : ‖(r : ℂ)‖ < 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1] using hr.2
    let f := CompositionDisk.coefficient 1 tail
    have hfp (n : ℕ) : 0 < f n := (CompositionDisk.source_series 1 tail).1 n
    have hseries := ((CompositionDisk.source_series 1 tail).2.2.1 (r : ℂ) hrc).of_norm.hasSum
    have hreal := Complex.reCLM.hasSum hseries
    have hs : Summable (fun n ↦ f n * r ^ n) := by
      simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, ← Complex.ofReal_pow, mul_zero, sub_zero, f] using hreal.summable
    let x := ∑' n : ℕ, f n * r ^ n
    have hx : 0 < x := by
      have ht := hs.sum_le_tsum {0}
        (fun n _ ↦ mul_nonneg (hfp n).le (pow_nonneg hr.1.le n))
      have ht' : f 0 ≤ x := by simpa only [Finset.sum_singleton, pow_zero, mul_one, x] using ht
      exact (hfp 0).trans_le ht'
    have hnorm : CompositionDisk.normalized 1 tail (r : ℂ) = (x : ℂ) := by
      apply HasSum.unique hseries
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_pow, f, x]
        using Complex.ofRealCLM.hasSum hs.hasSum
    have hsource : CompositionContinuation.continued ((1 : ℕ+) :: tail) (r : ℂ) =
        ((r ^ CompositionDisk.depth tail * x : ℝ) : ℂ) := by
      rw [(CompositionSlit.result.2.1 _).2 _ hrc,
        ← (CompositionDisk.source_series 1 tail).2.2.2.2.1 _ hrc,
        CompositionDisk.li, hnorm]
      push_cast
      rfl
    have hden : r ^ CompositionDisk.depth tail * x ≤
        D * (1 + ‖-Complex.log (1 - (r : ℂ))‖)^N := by
      have hsp : (1 : ℂ) - (r : ℂ) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; left; simpa using sub_pos.mpr hr.2
      have hb := hbound' (1 - (r : ℂ)) hsp
        (norm_pos_iff.mpr (Complex.slitPlane_ne_zero hsp)) hsmall
      have he : (1 : ℂ) - (1 - (r : ℂ)) = (r : ℂ) := by ring
      rw [he, hsource, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos (pow_pos hr.1 _) hx)] at hb
      exact hb
    have hdenpow := pow_le_pow_left₀ (mul_nonneg (pow_nonneg hr.1.le _) hx.le) hden (ell : ℕ)
    have hd' : D ^ (ell : ℕ) * (1-r) *
        (1 + ‖-Complex.log (1 - (r : ℂ))‖) ^ (N * (ell : ℕ)) < 1/2 := by
      have hwreal : ‖(1 : ℂ) - (r : ℂ)‖ = 1-r := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hr.2)]
      simpa only [Function.comp_def, hwreal] using hd
    have hscaled : (r ^ CompositionDisk.depth tail * x) ^ (ell : ℕ) * (1-r) ≤
        D ^ (ell : ℕ) * (1-r) *
          (1 + ‖-Complex.log (1 - (r : ℂ))‖) ^ (N * (ell : ℕ)) := by
      calc
        _ ≤ (D * (1 + ‖-Complex.log (1 - (r : ℂ))‖)^N) ^ (ell : ℕ) * (1-r) :=
          mul_le_mul_of_nonneg_right hdenpow (sub_pos.mpr hr.2).le
        _ = _ := by rw [mul_pow, ← pow_mul]; ring
    have hcancel : x ^ (ell : ℕ) * (1-r) ≤ 1 := by
      have hn0 : 0 < r ^ (CompositionDisk.depth tail * (ell : ℕ)) := pow_pos hr.1 _
      apply (mul_le_mul_iff_right₀ hn0).mp
      rw [mul_one]
      have he : r ^ (CompositionDisk.depth tail * (ell : ℕ)) *
          (x ^ (ell : ℕ) * (1-r)) =
          (r ^ CompositionDisk.depth tail * x) ^ (ell : ℕ) * (1-r) := by
        rw [mul_pow, ← pow_mul]; ring
      rw [he]
      exact (hscaled.trans hd'.le).trans hn.le
    have hA : (FiniteSlitCompositionMoments.reciprocal 1 tail ell (r : ℂ)).re =
        x⁻¹ ^ (ell : ℕ) := by
      rw [FiniteSlitCompositionMoments.reciprocal,
        (CompositionZeroFreeCollar.result 1 tail).1 _ hrc, hnorm]
      simp only [← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [hA, FiniteSlitOrdinaryEndpoint.endpoint]
    norm_num only [PNat.val_ofNat, lt_self_iff_false, ↓reduceIte, sub_zero]
    apply (le_div_iff₀ (sub_pos.mpr hr.2)).mpr
    simp only [one_mul, inv_pow]
    simpa only [one_div] using
      ((le_div_iff₀ (pow_pos hx (ell : ℕ))).mpr (by nlinarith [hcancel]) :
        1-r ≤ 1 / x ^ (ell : ℕ))

/-- The unchanged Xu--Zhao event for every positive composition and reciprocal power,
including all fixed positive smoothing orders and the strict admissible baseline. -/
theorem full_result (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) :
    (∀ᶠ n : ℕ in atTop,
      PowerSeries.coeff n (FiniteSlitOrdinaryCoefficients.ordinary head tail ell) < 0) ∧
    (∀ j : ℕ, 1 ≤ j → ∀ᶠ n : ℕ in atTop,
      0 < smooth (FiniteSlitOrdinaryCoefficients.ordinary head tail ell) j n) ∧
    (1 < (head : ℕ) → ∀ j : ℕ, 1 ≤ j → ∀ᶠ n : ℕ in atTop,
      (CompositionBoundary.zeta head tail)⁻¹ ^ (ell : ℕ) *
        (Nat.choose (n+j-1) n : ℝ) <
          smooth (FiniteSlitOrdinaryCoefficients.ordinary head tail ell) j n) := by
  by_cases hh : 1 < (head : ℕ)
  · have h := result head tail ell hh
    exact ⟨h.1, fun j hj ↦ (h.2 j hj).mono (fun _ hn ↦ hn.1),
      fun _ j hj ↦ (h.2 j hj).mono (fun _ hn ↦ hn.2)⟩
  · have hhead : head = (1 : ℕ+) := Subtype.ext (by change (head : ℕ) = 1; have := head.pos; omega)
    subst head
    let p := FiniteSlitOrdinaryCoefficients.ordinary 1 tail ell
    let L := FiniteSlitOrdinaryEndpoint.endpoint 1 tail ell
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < smooth (p - PowerSeries.C L) 1 n := by
      filter_upwards [(FiniteSlitOrdinaryEndpoint.result 1 tail ell).2.2] with n hn
      rw [first]
      exact sub_pos.mpr hn
    have hall := FiniteSlitOrdinarySmoothing.result p L
      (fun r ↦ ((FiniteSlitCompositionMoments.reciprocal 1 tail ell (r : ℂ)).re - L)/(1-r))
      hpos (first_series 1 tail ell) (leading_one_margin tail ell)
    refine ⟨(FiniteSlitOrdinaryCoefficients.result 1 tail ell).2.2, ?_, fun h ↦ (hh h).elim⟩
    intro j hj
    simpa [L, FiniteSlitOrdinaryEndpoint.endpoint] using hall j hj

#print axioms full_result

end D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitAdmissibleSmoothing
