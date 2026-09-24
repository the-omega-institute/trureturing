/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionBanks
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/CompositionBanks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Endpoint limits and strict conjugate banks for the actual positive-composition branch. -/

import D5.S3.AnalyticClosure.Polylogarithm.CompositionBoundary
import D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksIntegralControl
import D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksLeadingTransport
import D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksLeadingClosure
import D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksOrdinaryTransport
import D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksSourceInduction
import D5.S3.AnalyticClosure.Polylogarithm.CompositionSlit
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.ExtendFrom

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Interval ComplexConjugate

namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionBanks

open CompositionDisk CompositionBoundary CompositionContinuation

open private radial_div_bound radial_one_sub_bound
  radial_majorant_integrable radial_majorant_integral_le radial_div_integral_bound
  radial_one_sub_integral_bound radial_div_uniform_bound radial_one_sub_uniform_bound
  inner_arc_decay from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksIntegralControl
open private polynomialPrimitive leading_remainder_integral_identity split_leading_ones from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksLeadingTransport
open private slit_remainder_majorant_tendsto_zero
  admissible_reciprocal_endpoint_of_remainder
  leading_one_continued_norm_bound_of_remainder
  leading_one_reciprocal_endpoint_of_remainder
  leading_one_upper_boundary_reciprocal_im_eventually_neg
  leading_one_upper_boundary_pow_im_eventually_pos_of_extension
  polynomial_upper_pow_im_eventually_ge
  leading_one_upper_boundary_remainder_of_extension
  leading_one_upper_boundary_pow_remainder_of_extension leading_one_remainder_iterate
  composition_continued_norm_bound from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksLeadingClosure
open private ordinary_admissible_remainder_step from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksOrdinaryTransport
open private actual_upper_bank_atlas composition_remainder_cases_of_controls from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksSourceInduction
open private sourceWeight admissibleRemainder suffixConstant
  leadingOneRemainder from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksSourceInduction
/-- The actual normalized reciprocal has its common endpoint and strict conjugate
banks throughout a sufficiently small closed half-collar of the principal slit. -/
theorem result (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) :
    let A : ℂ → ℂ := fun z ↦
      (z ^ CompositionDisk.depth tail /
        CompositionContinuation.continued (head :: tail) z) ^ (ell : ℕ)
    let endpoint : ℂ :=
      if 1 < (head : ℕ) then
        ((CompositionBoundary.zeta head tail : ℂ)⁻¹) ^ (ell : ℕ)
      else 0
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      (∀ z ∈ CompositionContinuation.omega, ‖z - 1‖ ≤ ρ →
        CompositionContinuation.continued (head :: tail) z ≠ 0) ∧
      Tendsto A (nhdsWithin 1 CompositionContinuation.omega) (nhds endpoint) ∧
      ∃ upper lower : ℂ → ℂ,
        ContinuousOn upper {z | ‖z - 1‖ ≤ ρ ∧ 0 ≤ z.im} ∧
        ContinuousOn lower {z | ‖z - 1‖ ≤ ρ ∧ z.im ≤ 0} ∧
        (∀ z, ‖z - 1‖ ≤ ρ → 0 ≤ z.im → z ∈ CompositionContinuation.omega →
          upper z = A z) ∧
        (∀ z, ‖z - 1‖ ≤ ρ → z.im ≤ 0 → z ∈ CompositionContinuation.omega →
          lower z = A z) ∧
        upper 1 = endpoint ∧ lower 1 = endpoint ∧
        (∀ z, ‖z - 1‖ ≤ ρ → z.im ≤ 0 →
          lower z = conj (upper (conj z))) ∧
        ∀ t : ℝ, 0 < t → t ≤ ρ → (upper (1 + (t : ℂ))).im < 0 := by
  dsimp only
  classical
  obtain ⟨_continued_nil, continued_analytic, continued_source, _leading_deriv,
      _ordinary_deriv⟩ := CompositionSlit.result
  obtain ⟨actualUpperBank, actual_upper_local_extension_with_limit,
      actual_upper_bank_local_trace, actual_upper_ordinary_pair⟩ :=
    actual_upper_bank_atlas
  have actual_upper_bank_ordinary_deriv : ∀ (first : ℕ+) (suffix : List ℕ+)
      (hfirst : 1 < (first : ℕ)) (x : ℝ),
      1 < x →
      HasDerivAt (fun y : ℝ ↦ (actualUpperBank (first :: suffix) y).im)
        ((actualUpperBank (⟨(first : ℕ) - 1, by omega⟩ :: suffix) x).im / x) x := by
    intro first suffix hfirst x hx
    obtain ⟨r, hr, _hr1, F, G, hF, hG, hFactual, hGactual, hFderiv⟩ :=
      actual_upper_ordinary_pair first suffix hfirst x 1 hx zero_lt_one
    obtain ⟨δF, hδF, hFtrace⟩ :=
      actual_upper_bank_local_trace (first :: suffix) x r F hx hr hF hFactual
    obtain ⟨δG, hδG, hGtrace⟩ := actual_upper_bank_local_trace
      (⟨(first : ℕ) - 1, by omega⟩ :: suffix) x r G hx hr hG hGactual
    have hcomplex := hFderiv (x : ℂ) (Metric.mem_ball_self hr)
    have hreal := hcomplex.comp_ofReal
    have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hreal
    have hFeq : (fun y : ℝ ↦ (actualUpperBank (first :: suffix) y).im) =ᶠ[𝓝 x]
        (fun y : ℝ ↦ (F (y : ℂ)).im) := by
      filter_upwards [Metric.ball_mem_nhds x hδF] with y hy
      exact congrArg Complex.im (hFtrace y (by simpa only [Metric.mem_ball] using hy)).symm
    have hderiv := him.congr_of_eventuallyEq hFeq
    have hGx : G (x : ℂ) =
        actualUpperBank (⟨(first : ℕ) - 1, by omega⟩ :: suffix) x :=
      hGtrace x (by simpa using hδG)
    rw [← hGx]
    have hx0 : x ≠ 0 := by linarith
    have hcoeff : Complex.imCLM (G (x : ℂ) / (x : ℂ)) = (G (x : ℂ)).im / x := by
      rw [Complex.imCLM_apply, Complex.div_im, Complex.normSq_apply]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]
      field_simp
      ring
    simpa only [Function.comp_apply, Complex.imCLM_apply] using
      hderiv.congr_deriv hcoeff
  have composition_remainder_cases (first : ℕ+) (suffix : List ℕ+) :=
    composition_remainder_cases_of_controls first suffix composition_continued_norm_bound
      ordinary_admissible_remainder_step
      leading_one_remainder_iterate split_leading_ones

  have leading_one_upper_sign : (head : ℕ) = 1 →
      ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ (center : ℂ) (r : ℝ) (extension : ℂ → ℂ) (value : ℂ),
        (1 + (t : ℂ)) ∈ Metric.ball center r →
        AnalyticOnNhd ℂ extension (Metric.ball center r) →
        Set.EqOn extension (CompositionContinuation.continued (head :: tail))
          (Metric.ball center r ∩ {z : ℂ | 0 < z.im}) →
        value = (((1 + (t : ℂ)) ^ CompositionDisk.depth tail /
          extension (1 + (t : ℂ))) ^ (ell : ℕ)) → value.im < 0 := by
    intro hhead
    rcases composition_remainder_cases head tail with hadmissible | hleading
    · omega
    · obtain ⟨q, suffix, _hhead, hq, hcomposition, _hsuffix, hremainder⟩ := hleading
      dsimp only [leadingOneRemainder] at hremainder
      obtain ⟨hsuffix, ρ, C, M, P, hρ0, _hρ1, hC, hdegree, hcoeff, hbound⟩ := hremainder
      have hlead : 0 < P.coeff q := by
        rw [hcoeff]
        have hsuffix_pos : 0 < suffixConstant suffix := by
          rcases hsuffix with rfl | ⟨first, rest, rfl, hfirst⟩
          · simp [suffixConstant]
          · simpa [suffixConstant] using
              (CompositionBoundary.result first rest hfirst).2.2.2.1
        exact div_pos hsuffix_pos (by positivity)
      simpa only [← hcomposition] using
        (leading_one_upper_boundary_reciprocal_im_eventually_neg q (ell : ℕ)
          (CompositionDisk.depth tail) suffix ρ C M P hq ell.property hρ0 hC
          hdegree hlead hbound)
  have admissible_reciprocal_endpoint : ∀ (first : ℕ+) (suffix : List ℕ+),
      admissibleRemainder first suffix →
        Tendsto
            (fun w : ℂ ↦ CompositionContinuation.continued (first :: suffix) (1 - w))
            (𝓝[Complex.slitPlane] 0)
            (𝓝 (CompositionBoundary.zeta first suffix : ℂ)) ∧
          (∀ᶠ w : ℂ in 𝓝[Complex.slitPlane] 0,
            CompositionContinuation.continued (first :: suffix) (1 - w) ≠ 0) ∧
          Tendsto
            (fun w : ℂ ↦ (((1 - w) ^ CompositionDisk.depth suffix /
              CompositionContinuation.continued (first :: suffix) (1 - w)) ^ (ell : ℕ)))
            (𝓝[Complex.slitPlane] 0)
            (𝓝 (((CompositionBoundary.zeta first suffix : ℂ)⁻¹) ^ (ell : ℕ))) := by
    intro first suffix hremainder
    dsimp only [admissibleRemainder] at hremainder
    obtain ⟨hfirst, ρ, C, M, hρ0, _, hC, hbound⟩ := hremainder
    exact admissible_reciprocal_endpoint_of_remainder first suffix (ell : ℕ)
      C ρ M hfirst hC hρ0 hbound
  have leading_one_reciprocal_endpoint : ∀ (q : ℕ) (suffix : List ℕ+),
      1 ≤ q → leadingOneRemainder q suffix →
        Tendsto
            (fun w : ℂ ↦ ‖CompositionContinuation.continued
              (List.replicate q (1 : ℕ+) ++ suffix) (1 - w)‖)
            (𝓝[Complex.slitPlane] 0) atTop ∧
          (∀ᶠ w : ℂ in 𝓝[Complex.slitPlane] 0,
            CompositionContinuation.continued
              (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) ≠ 0) ∧
          Tendsto
            (fun w : ℂ ↦ (((1 - w) ^ CompositionDisk.depth
                (List.replicate (q - 1) (1 : ℕ+) ++ suffix) /
              CompositionContinuation.continued
                (List.replicate q (1 : ℕ+) ++ suffix) (1 - w)) ^ (ell : ℕ)))
            (𝓝[Complex.slitPlane] 0) (𝓝 0) := by
    intro q suffix hq hremainder
    dsimp only [leadingOneRemainder] at hremainder
    obtain ⟨_hsuffix, ρ, C, M, P, hρ0, _, hC, hdegree, _hcoeff, hbound⟩ :=
      hremainder
    exact leading_one_reciprocal_endpoint_of_remainder q (ell : ℕ) suffix
      ρ C M P hq ell.property hρ0 hC hdegree hbound

  have composition_reciprocal_endpoint :
      (∀ᶠ w : ℂ in 𝓝[Complex.slitPlane] 0,
        CompositionContinuation.continued (head :: tail) (1 - w) ≠ 0) ∧
      Tendsto
        (fun w : ℂ ↦ (((1 - w) ^ CompositionDisk.depth tail /
          CompositionContinuation.continued (head :: tail) (1 - w)) ^ (ell : ℕ)))
        (𝓝[Complex.slitPlane] 0)
        (𝓝 (if 1 < (head : ℕ) then
          ((CompositionBoundary.zeta head tail : ℂ)⁻¹) ^ (ell : ℕ) else 0)) := by
    rcases composition_remainder_cases head tail with hadmissible | hleading
    · obtain ⟨hfirst, hremainder⟩ := hadmissible
      obtain ⟨_hcontinued, hnonzero, hendpoint⟩ :=
        admissible_reciprocal_endpoint head tail hremainder
      exact ⟨hnonzero, by simpa [hfirst] using hendpoint⟩
    · obtain ⟨q, suffix, hhead, hq, hcomposition, _hsuffix, hremainder⟩ := hleading
      subst head
      obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hq
      have hqeq : 1 + q = q + 1 := by omega
      rw [hqeq] at hcomposition hremainder
      have htail : tail = List.replicate q (1 : ℕ+) ++ suffix := by
        simpa [List.replicate_succ] using hcomposition
      obtain ⟨_hnorm, hnonzero, hendpoint⟩ :=
        leading_one_reciprocal_endpoint (q + 1) suffix (by omega) hremainder
      refine ⟨?_, ?_⟩
      · simpa [List.replicate_succ, htail] using hnonzero
      · simpa [List.replicate_succ, htail] using hendpoint

  have upper_half_ball_mem_closure : ∀ (x r : ℝ), 0 < r →
      (x : ℂ) ∈ closure (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) := by
    intro x r hr
    rw [Metric.mem_closure_iff]
    intro ε hε
    let δ : ℝ := min (r / 2) (ε / 2)
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    let y : ℂ := (x : ℂ) + (δ : ℝ) * I
    have hdist : dist y (x : ℂ) = δ := by
      rw [dist_eq_norm]
      simp only [y, add_sub_cancel_left, norm_mul, norm_real, norm_I]
      rw [Real.norm_eq_abs, abs_of_pos hδ, mul_one]
    refine ⟨y, ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, hdist]
      exact (min_le_left _ _).trans_lt (half_lt_self hr)
    · simpa [y] using hδ
    · rw [dist_comm, hdist]
      exact (min_le_right _ _).trans_lt (half_lt_self hε)

  have actual_upper_bank_endpoint : ∀ (first : ℕ+) (suffix : List ℕ+),
      1 < (first : ℕ) →
      Tendsto (fun x : ℝ ↦ actualUpperBank (first :: suffix) x) (𝓝[>] 1)
        (𝓝 (CompositionBoundary.zeta first suffix : ℂ)) := by
    intro first suffix hfirst
    obtain ⟨_hfirst, hremainder⟩ := (composition_remainder_cases first suffix).resolve_right (by
      rintro ⟨_q, _rest, hfirstOne, _hq, _hcomposition, _hrest, _hremainder⟩
      have himpossible : 1 < (((1 : ℕ+) : ℕ)) := hfirstOne ▸ hfirst
      norm_num at himpossible)
    obtain ⟨hcontinued, _hnonzero, _hreciprocal⟩ :=
      admissible_reciprocal_endpoint first suffix hremainder
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hclose : ∀ᶠ w : ℂ in 𝓝[Complex.slitPlane] 0,
        dist (CompositionContinuation.continued (first :: suffix) (1 - w))
          (CompositionBoundary.zeta first suffix : ℂ) < ε / 2 :=
      hcontinued (Metric.ball_mem_nhds _ (half_pos hε))
    change {w : ℂ | dist
      (CompositionContinuation.continued (first :: suffix) (1 - w))
        (CompositionBoundary.zeta first suffix : ℂ) < ε / 2} ∈
      𝓝[Complex.slitPlane] 0 at hclose
    obtain ⟨s, hs, hsubset⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hclose
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
    filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 1 + δ / 4 by linarith)] with x hx
    obtain ⟨r, hr, hrδ, extension, hextension, _heq, hlimit⟩ :=
      actual_upper_local_extension_with_limit (first :: suffix) x (δ / 4)
        hx.1 (by positivity)
    obtain ⟨η, hη, htrace⟩ := actual_upper_bank_local_trace
      (first :: suffix) x r extension hx.1 hr hextension _heq
    have hbound : ∀ z ∈ Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im},
        dist (CompositionContinuation.continued (first :: suffix) z)
          (CompositionBoundary.zeta first suffix : ℂ) < ε / 2 := by
      intro z hz
      have hwball : 1 - z ∈ Metric.ball (0 : ℂ) δ := by
        rw [Metric.mem_ball, dist_zero_right]
        calc
          ‖1 - z‖ = ‖z - 1‖ := by
            rw [← norm_neg (1 - z)]
            congr 2
            ring
          _ ≤ ‖z - (x : ℂ)‖ + ‖(x : ℂ) - 1‖ := by
            have : z - 1 = (z - (x : ℂ)) + ((x : ℂ) - 1) := by ring
            rw [this]
            exact norm_add_le _ _
          _ < r + (x - 1) := by
            have hzx : ‖z - (x : ℂ)‖ < r := by
              simpa only [Metric.mem_ball, dist_eq_norm] using hz.1
            have hxnorm : ‖(x : ℂ) - 1‖ = x - 1 := by
              rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
                Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hx.1)]
            rw [hxnorm]
            linarith
          _ < δ := by linarith [hrδ, hx.2]
      have hwslit : 1 - z ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]
        right
        simp only [sub_im, one_im, zero_sub, neg_ne_zero]
        exact ne_of_gt hz.2
      have hw := hsubset ⟨hball hwball, hwslit⟩
      change dist
        (CompositionContinuation.continued (first :: suffix) (1 - (1 - z)))
          (CompositionBoundary.zeta first suffix : ℂ) < ε / 2 at hw
      simpa only [sub_sub_cancel] using hw
    haveI : NeBot
        (𝓝[(Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im})] (x : ℂ)) :=
      mem_closure_iff_nhdsWithin_neBot.mp (upper_half_ball_mem_closure x r hr)
    have hdistLimit : Tendsto
        (fun z : ℂ ↦ dist (CompositionContinuation.continued (first :: suffix) z)
          (CompositionBoundary.zeta first suffix : ℂ))
        (𝓝[(Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im})] (x : ℂ))
        (𝓝 (dist (extension (x : ℂ))
          (CompositionBoundary.zeta first suffix : ℂ))) :=
      hlimit.dist tendsto_const_nhds
    have hclosed : dist (extension (x : ℂ))
        (CompositionBoundary.zeta first suffix : ℂ) ≤ ε / 2 :=
      isClosed_Iic.mem_of_tendsto hdistLimit <| by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (hbound z hz).le
    rw [← htrace x (by simpa using hη)]
    exact hclosed.trans_lt (half_lt_self hε)
  have composition_continued_norm_margin : ∃ δ c : ℝ,
      0 < δ ∧ 0 < c ∧
        ∀ z ∈ CompositionContinuation.omega, ‖z - 1‖ < δ →
          c ≤ ‖CompositionContinuation.continued (head :: tail) z‖ := by
    rcases composition_remainder_cases head tail with hadmissible | hleading
    · obtain ⟨hfirst, hremainder⟩ := hadmissible
      obtain ⟨hcontinued, _hnonzero, _hendpoint⟩ :=
        admissible_reciprocal_endpoint head tail hremainder
      let Z : ℂ := (CompositionBoundary.zeta head tail : ℂ)
      have hZpos : 0 < ‖Z‖ := norm_pos_iff.mpr <| by
        exact ofReal_ne_zero.mpr <| ne_of_gt (CompositionBoundary.result head tail hfirst).2.2.2.1
      have hclose : ∀ᶠ w : ℂ in 𝓝[Complex.slitPlane] 0,
          dist (CompositionContinuation.continued (head :: tail) (1 - w)) Z < ‖Z‖ / 2 :=
        hcontinued (Metric.ball_mem_nhds Z (half_pos hZpos))
      have hlower : ∀ᶠ w : ℂ in 𝓝[Complex.slitPlane] 0,
          ‖Z‖ / 2 ≤ ‖CompositionContinuation.continued (head :: tail) (1 - w)‖ := by
        filter_upwards [hclose] with w hw
        have htriangle : ‖Z‖ ≤
            dist (CompositionContinuation.continued (head :: tail) (1 - w)) Z +
              ‖CompositionContinuation.continued (head :: tail) (1 - w)‖ := by
          rw [dist_eq_norm]
          calc
            ‖Z‖ = ‖(Z - CompositionContinuation.continued (head :: tail) (1 - w)) +
                CompositionContinuation.continued (head :: tail) (1 - w)‖ := by ring_nf
            _ ≤ ‖Z - CompositionContinuation.continued (head :: tail) (1 - w)‖ +
                ‖CompositionContinuation.continued (head :: tail) (1 - w)‖ := norm_add_le _ _
            _ = ‖CompositionContinuation.continued (head :: tail) (1 - w) - Z‖ +
                ‖CompositionContinuation.continued (head :: tail) (1 - w)‖ := by
                  rw [← norm_neg (Z - _)]
                  congr 2
                  ring
        linarith
      change {w : ℂ | ‖Z‖ / 2 ≤
        ‖CompositionContinuation.continued (head :: tail) (1 - w)‖} ∈
          𝓝[Complex.slitPlane] 0 at hlower
      obtain ⟨s, hs, hsubset⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hlower
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
      refine ⟨δ, ‖Z‖ / 2, hδ, half_pos hZpos, ?_⟩
      intro z hz hzδ
      have hwslit : 1 - z ∈ Complex.slitPlane := hz
      have hwball : (1 : ℂ) - z ∈ Metric.ball (0 : ℂ) δ := by
        rw [Metric.mem_ball, dist_zero_right, ← norm_neg (1 - z)]
        simpa only [neg_sub] using hzδ
      have := hsubset ⟨hball hwball, hwslit⟩
      change ‖Z‖ / 2 ≤ ‖CompositionContinuation.continued
        (head :: tail) (1 - (1 - z))‖ at this
      simpa only [sub_sub_cancel] using this
    · obtain ⟨q, suffix, hhead, hq, hcomposition, _hsuffix, hremainder⟩ := hleading
      subst head
      obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hq
      have hqeq : 1 + q = q + 1 := by omega
      rw [hqeq] at hcomposition hremainder
      have htail : tail = List.replicate q (1 : ℕ+) ++ suffix := by
        simpa [List.replicate_succ] using hcomposition
      obtain ⟨hnorm, _hnonzero, _hendpoint⟩ :=
        leading_one_reciprocal_endpoint (q + 1) suffix (by omega) hremainder
      have hlower : ∀ᶠ w : ℂ in 𝓝[Complex.slitPlane] 0,
          (2 : ℝ) ≤ ‖CompositionContinuation.continued
            (List.replicate (q + 1) (1 : ℕ+) ++ suffix) (1 - w)‖ :=
        hnorm.eventually (eventually_ge_atTop 2)
      change {w : ℂ | (2 : ℝ) ≤ ‖CompositionContinuation.continued
        (List.replicate (q + 1) (1 : ℕ+) ++ suffix) (1 - w)‖} ∈
          𝓝[Complex.slitPlane] 0 at hlower
      obtain ⟨s, hs, hsubset⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hlower
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
      refine ⟨δ, 2, hδ, by norm_num, ?_⟩
      intro z hz hzδ
      have hwslit : 1 - z ∈ Complex.slitPlane := hz
      have hwball : (1 : ℂ) - z ∈ Metric.ball (0 : ℂ) δ := by
        rw [Metric.mem_ball, dist_zero_right, ← norm_neg (1 - z)]
        simpa only [neg_sub] using hzδ
      have := hsubset ⟨hball hwball, hwslit⟩
      simpa [List.replicate_succ, htail] using this

  have actual_upper_boundary_nonzero : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ x : ℝ, 1 < x → x - 1 ≤ ρ →
        ∃ r : ℝ, 0 < r ∧
          ∃ extension : ℂ → ℂ,
            AnalyticOnNhd ℂ extension (Metric.ball (x : ℂ) r) ∧
              Set.EqOn extension (CompositionContinuation.continued (head :: tail))
                (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
              extension (x : ℂ) ≠ 0 := by
    obtain ⟨δ, c, hδ, hc, hlower⟩ := composition_continued_norm_margin
    let ρ : ℝ := min (δ / 4) (1 / 2)
    have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
    have hρ1 : ρ < 1 := (min_le_right _ _).trans_lt (by norm_num)
    refine ⟨ρ, hρ0, hρ1, ?_⟩
    intro x hx hxρ
    obtain ⟨r, hr, hrδ, extension, hextension, heq, hlimit⟩ :=
      actual_upper_local_extension_with_limit (head :: tail) x (δ / 4) hx (by positivity)
    refine ⟨r, hr, extension, hextension, heq, ?_⟩
    have hballMargin : ∀ z ∈
        Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im},
        c ≤ ‖CompositionContinuation.continued (head :: tail) z‖ := by
      intro z hz
      have hzo : z ∈ CompositionContinuation.omega := by
        change 1 - z ∈ Complex.slitPlane
        rw [Complex.mem_slitPlane_iff]
        right
        simp only [sub_im, one_im, zero_sub, neg_ne_zero]
        exact ne_of_gt hz.2
      apply hlower z hzo
      calc
        ‖z - 1‖ ≤ ‖z - (x : ℂ)‖ + ‖(x : ℂ) - 1‖ := by
          have hzdecomp : z - 1 = (z - (x : ℂ)) + ((x : ℂ) - 1) := by ring
          rw [hzdecomp]
          exact norm_add_le _ _
        _ < r + (x - 1) := by
          have hzx : ‖z - (x : ℂ)‖ < r := by
            simpa only [Metric.mem_ball, dist_eq_norm] using hz.1
          have hnormx : ‖(x : ℂ) - 1‖ = x - 1 := by
            rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hx)]
          rw [hnormx]
          linarith
        _ < δ := by
          have hrδ' : r < δ / 4 := hrδ
          have hxδ : x - 1 ≤ δ / 4 := hxρ.trans (min_le_left _ _)
          linarith
    haveI : NeBot
        (𝓝[(Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im})] (x : ℂ)) :=
      mem_closure_iff_nhdsWithin_neBot.mp (upper_half_ball_mem_closure x r hr)
    have hnormLimit : Tendsto
        (fun z : ℂ ↦ ‖CompositionContinuation.continued (head :: tail) z‖)
        (𝓝[(Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im})] (x : ℂ))
        (𝓝 ‖extension (x : ℂ)‖) := hlimit.norm
    have hclosed : c ≤ ‖extension (x : ℂ)‖ :=
      isClosed_Ici.mem_of_tendsto hnormLimit <| by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact hballMargin z hz
    exact norm_ne_zero_iff.mp (ne_of_gt (hc.trans_le hclosed))

  have leading_one_actual_upper_bank_im_eventually_pos :
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        0 < (actualUpperBank ((1 : ℕ+) :: tail) (1 + t)).im := by
    rcases composition_remainder_cases (1 : ℕ+) tail with hadmissible |
      ⟨q, suffix, _hhead, hq, hcomposition, _hsuffix, hremainder⟩
    · have himpossible := hadmissible.1
      norm_num at himpossible
    · dsimp only [leadingOneRemainder] at hremainder
      obtain ⟨hsuffix, ρ, C, M, P, hρ0, _hρ1, hC, hdegree, hcoeff, hbound⟩ :=
        hremainder
      have hlead : 0 < P.coeff q := by
        rw [hcoeff]
        have hsuffix_pos : 0 < suffixConstant suffix := by
          rcases hsuffix with rfl | ⟨first, rest, rfl, hfirst⟩
          · simp [suffixConstant]
          · simpa [suffixConstant] using
              (CompositionBoundary.result first rest hfirst).2.2.2.1
        exact div_pos hsuffix_pos (by positivity)
      have hsign := leading_one_upper_boundary_pow_im_eventually_pos_of_extension
        q 1 suffix ρ C M P hq (by omega) hρ0 hC hdegree hlead hbound
      filter_upwards [hsign, self_mem_nhdsWithin] with t ht ht0
      have htpos : 0 < t := ht0
      obtain ⟨r, hr, _hr1, extension, hextension, heq, _hlimit⟩ :=
        actual_upper_local_extension_with_limit
          ((1 : ℕ+) :: tail) (1 + t) 1
            (by linarith) zero_lt_one
      obtain ⟨δ, hδ, htrace⟩ := actual_upper_bank_local_trace
        ((1 : ℕ+) :: tail) (1 + t) r extension
          (by linarith) hr hextension heq
      have heq' : Set.EqOn extension
          (CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix))
          (Metric.ball ((1 + t : ℝ) : ℂ) r ∩ {z : ℂ | 0 < z.im}) := by
        simpa only [← hcomposition] using heq
      have hcenter : 1 + (t : ℂ) ∈ Metric.ball ((1 + t : ℝ) : ℂ) r := by
        convert Metric.mem_ball_self hr using 1 <;> norm_num
      have hpositive := ht ((1 + t : ℝ) : ℂ) r extension hcenter hextension heq'
      have hvalue := htrace (1 + t) (by simpa using hδ)
      rw [← hvalue]
      simpa only [pow_one, ofReal_add, ofReal_one] using hpositive

  have actual_upper_bank_im_eventually_pos : ∀ first : ℕ+,
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        0 < (actualUpperBank (first :: tail) (1 + t)).im := by
    intro first
    have hall : ∀ (n : ℕ) (hn : 1 ≤ n),
        ∀ᶠ t : ℝ in 𝓝[>] 0,
          0 < (actualUpperBank ((⟨n, by omega⟩ : ℕ+) :: tail) (1 + t)).im := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro hn
          by_cases hn1 : n = 1
          · subst n
            simpa using leading_one_actual_upper_bank_im_eventually_pos
          · have hn2 : 1 < n := by omega
            let current : ℕ+ := ⟨n, by omega⟩
            let previous : ℕ+ := ⟨n - 1, by omega⟩
            have hprevious : ∀ᶠ t : ℝ in 𝓝[>] 0,
                0 < (actualUpperBank (previous :: tail) (1 + t)).im := by
              simpa only [previous] using ih (n - 1) (by omega) (by omega)
            change {t : ℝ |
              0 < (actualUpperBank (previous :: tail) (1 + t)).im} ∈
                𝓝[>] 0 at hprevious
            obtain ⟨u, hu, huprevious⟩ :=
              mem_nhdsGT_iff_exists_Ioo_subset.mp hprevious
            filter_upwards [Ioo_mem_nhdsGT hu] with t ht
            let f : ℝ → ℝ := fun x ↦ (actualUpperBank (current :: tail) x).im
            let f' : ℝ → ℝ := fun x ↦
              (actualUpperBank (previous :: tail) x).im / x
            have hcurrent : 1 < (current : ℕ) := by
              dsimp only [current]
              exact hn2
            have hendpoint := actual_upper_bank_endpoint current tail hcurrent
            have hfa : Tendsto f (𝓝[>] 1) (𝓝 0) := by
              have him := Complex.imCLM.continuous.continuousAt.tendsto.comp hendpoint
              change Tendsto
                (Complex.imCLM ∘ fun x ↦ actualUpperBank (current :: tail) x)
                (𝓝[>] 1) (𝓝 0)
              exact him
            have hfb : Tendsto f (𝓝[<] (1 + t))
                (𝓝 (f (1 + t))) := by
              exact (actual_upper_bank_ordinary_deriv current tail hcurrent
                (1 + t) (by linarith [ht.1])).continuousAt.tendsto.mono_left
                  nhdsWithin_le_nhds
            have hga : Tendsto (fun x : ℝ ↦ x) (𝓝[>] 1) (𝓝 1) :=
              tendsto_id.mono_left nhdsWithin_le_nhds
            have hgb : Tendsto (fun x : ℝ ↦ x) (𝓝[<] (1 + t))
                (𝓝 (1 + t)) := tendsto_id.mono_left nhdsWithin_le_nhds
            have hderiv : ∀ x ∈ Set.Ioo (1 : ℝ) (1 + t), HasDerivAt f (f' x) x := by
              intro x hx
              have hactual := actual_upper_bank_ordinary_deriv current tail hcurrent x hx.1
              have hpreviousEq :
                  (⟨(current : ℕ) - 1, by omega⟩ : ℕ+) = previous := by
                apply Subtype.ext
                change n - 1 = n - 1
                rfl
              rw [hpreviousEq] at hactual
              exact hactual
            obtain ⟨c, hc, hmvt⟩ := exists_ratio_hasDerivAt_eq_ratio_slope'
              f f' (by simpa only [lt_add_iff_pos_right] using ht.1)
              (fun x : ℝ ↦ x) (fun _ : ℝ ↦ 1) hderiv
              (fun x _ ↦ hasDerivAt_id x) hfa hga hfb hgb
            have hpredecessor :
                0 < (actualUpperBank (previous :: tail) c).im := by
              have hpos := huprevious (show c - 1 ∈ Set.Ioo 0 u by
                constructor <;> linarith [hc.1, hc.2, ht.2])
              change 0 < (actualUpperBank (previous :: tail) (1 + (c - 1))).im at hpos
              convert hpos using 1 <;> ring
            have hf'pos : 0 < f' c := by
              exact div_pos hpredecessor (by linarith [hc.1])
            dsimp only [f] at hmvt ⊢
            dsimp only [f'] at hf'pos hmvt
            norm_num at hmvt
            dsimp only [current] at hmvt ⊢
            rw [← hmvt]
            exact mul_pos ht.1 hf'pos
    have hfirstEq : (⟨(first : ℕ), first.property⟩ : ℕ+) = first := Subtype.ext rfl
    simpa only [hfirstEq] using hall (first : ℕ) first.property

  have one_add_tendsto_right : Tendsto (fun t : ℝ ↦ 1 + t) (𝓝[>] 0) (𝓝[>] 1) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) (𝓝[>] 0) (𝓝 1) :=
          tendsto_const_nhds
      have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have ht := hone.add hid
      simpa only [add_zero] using ht
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      change 1 < 1 + t
      linarith

  have higher_head_actual_upper_reciprocal_im_eventually_neg
      (hhead : 1 < (head : ℕ)) :
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        ((((1 + (t : ℂ)) ^ CompositionDisk.depth tail /
          actualUpperBank (head :: tail) (1 + t)) ^ (ell : ℕ))).im < 0 := by
    have hbankEndpoint :=
      (actual_upper_bank_endpoint head tail hhead).comp one_add_tendsto_right
    have hrealPowerPos : ∀ n : ℕ, ∀ᶠ t : ℝ in 𝓝[>] 0,
        0 < ((actualUpperBank (head :: tail) (1 + t)) ^ n).re := by
      intro n
      have hpower := hbankEndpoint.pow n
      have hreal := Complex.reCLM.continuous.continuousAt.tendsto.comp hpower
      change Tendsto
        (fun t : ℝ ↦ ((actualUpperBank (head :: tail) (1 + t)) ^ n).re)
        (𝓝[>] 0) (𝓝 (((CompositionBoundary.zeta head tail : ℂ) ^ n).re)) at hreal
      have hlimit : 0 < (((CompositionBoundary.zeta head tail : ℂ) ^ n).re) := by
        simpa only [← ofReal_pow, ofReal_re] using
          pow_pos (CompositionBoundary.result head tail hhead).2.2.2.1 n
      exact hreal.eventually (Ioi_mem_nhds hlimit)
    have hbankIm := actual_upper_bank_im_eventually_pos head
    have hpowerIm : ∀ n : ℕ, 1 ≤ n → ∀ᶠ t : ℝ in 𝓝[>] 0,
        0 < ((actualUpperBank (head :: tail) (1 + t)) ^ n).im := by
      intro n hn
      induction n with
      | zero => omega
      | succ n ih =>
          by_cases hn0 : n = 0
          · subst n
            convert hbankIm using 1 <;> norm_num
          · have hprevious := ih (by omega)
            have hpreviousRe := hrealPowerPos n
            have hbankRe := hrealPowerPos 1
            filter_upwards [hprevious, hpreviousRe, hbankRe, hbankIm] with
              t hprevious hpreviousRe hbankRe hbankIm
            simp only [pow_one] at hbankRe
            rw [pow_succ, Complex.mul_im]
            exact add_pos (mul_pos hpreviousRe hbankIm) (mul_pos hprevious hbankRe)
    have hdenominatorIm := hpowerIm (ell : ℕ) ell.property
    filter_upwards [hdenominatorIm, self_mem_nhdsWithin] with t hdenominatorIm ht
    let numerator : ℂ := ((1 + (t : ℂ)) ^ CompositionDisk.depth tail) ^ (ell : ℕ)
    let denominator : ℂ := (actualUpperBank (head :: tail) (1 + t)) ^ (ell : ℕ)
    have htpos : 0 < t := ht
    have hreal : 1 + (t : ℂ) = ((1 + t : ℝ) : ℂ) := by norm_num
    have hnumeratorIm : numerator.im = 0 := by
      dsimp only [numerator]
      rw [hreal, ← ofReal_pow, ← ofReal_pow, ofReal_im]
    have hnumeratorRe : 0 < numerator.re := by
      dsimp only [numerator]
      rw [hreal, ← ofReal_pow, ← ofReal_pow, ofReal_re]
      exact pow_pos (pow_pos (by linarith) _) _
    change 0 < denominator.im at hdenominatorIm
    have hdenominatorNe : denominator ≠ 0 := by
      exact fun hzero ↦ by simpa [denominator, hzero] using hdenominatorIm
    have hnormSq : 0 < Complex.normSq denominator := Complex.normSq_pos.mpr hdenominatorNe
    rw [div_pow]
    change (numerator / denominator).im < 0
    rw [Complex.div_im, hnumeratorIm]
    simp only [zero_mul, zero_div, zero_sub]
    exact neg_neg_of_pos (div_pos (mul_pos hnumeratorRe hdenominatorIm) hnormSq)

  have actual_upper_reciprocal_im_eventually_neg :
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        ((((1 + (t : ℂ)) ^ CompositionDisk.depth tail /
          actualUpperBank (head :: tail) (1 + t)) ^ (ell : ℕ))).im < 0 := by
    by_cases hhead : (head : ℕ) = 1
    · have hsign := leading_one_upper_sign hhead
      filter_upwards [hsign, self_mem_nhdsWithin] with t hsign ht
      have htpos : 0 < t := ht
      obtain ⟨r, hr, _hr1, extension, hextension, heq, _hlimit⟩ :=
        actual_upper_local_extension_with_limit
          (head :: tail) (1 + t) 1 (by linarith) zero_lt_one
      obtain ⟨δ, hδ, htrace⟩ := actual_upper_bank_local_trace
        (head :: tail) (1 + t) r extension (by linarith) hr hextension heq
      have hcenter : 1 + (t : ℂ) ∈ Metric.ball ((1 + t : ℝ) : ℂ) r := by
        convert Metric.mem_ball_self hr using 1 <;> norm_num
      apply hsign ((1 + t : ℝ) : ℂ) r extension
        ((((1 + (t : ℂ)) ^ CompositionDisk.depth tail /
          actualUpperBank (head :: tail) (1 + t)) ^ (ell : ℕ)))
        hcenter hextension heq
      rw [← htrace (1 + t) (by simpa using hδ)]
      norm_num
    · have hpositive : 0 < (head : ℕ) := head.property
      exact higher_head_actual_upper_reciprocal_im_eventually_neg (by omega)

  have actual_upper_reciprocal_local_extension : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ x : ℝ, 1 < x → x - 1 ≤ ρ →
        ∃ r : ℝ, 0 < r ∧
          ∃ extension : ℂ → ℂ,
            AnalyticOnNhd ℂ extension (Metric.ball (x : ℂ) r) ∧
              Set.EqOn extension
                (fun z : ℂ ↦ ((z ^ CompositionDisk.depth tail /
                  CompositionContinuation.continued (head :: tail) z) ^ (ell : ℕ)))
                (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
              Tendsto
                (fun z : ℂ ↦ ((z ^ CompositionDisk.depth tail /
                  CompositionContinuation.continued (head :: tail) z) ^ (ell : ℕ)))
                (𝓝[(Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im})] (x : ℂ))
                (𝓝 (extension (x : ℂ))) ∧
              (extension (x : ℂ)).im < 0 := by
    obtain ⟨ρ, hρ0, hρ1, hboundary⟩ := actual_upper_boundary_nonzero
    change {t : ℝ | ((((1 + (t : ℂ)) ^ CompositionDisk.depth tail /
      actualUpperBank (head :: tail) (1 + t)) ^ (ell : ℕ))).im < 0} ∈
        𝓝[>] 0 at actual_upper_reciprocal_im_eventually_neg
    obtain ⟨δ, hδ, hδsign⟩ :=
      mem_nhdsGT_iff_exists_Ioo_subset.mp actual_upper_reciprocal_im_eventually_neg
    let ρ' : ℝ := min ρ (δ / 2)
    have hρ' : 0 < ρ' := by
      dsimp only [ρ']
      exact lt_min hρ0 (half_pos hδ)
    refine ⟨ρ', hρ', (min_le_left _ _).trans_lt hρ1, ?_⟩
    intro x hx hxρ
    obtain ⟨r, hr, continuedExtension, hcontinuedAnalytic, hcontinuedEq,
        hcontinuedNe⟩ := hboundary x hx (hxρ.trans (min_le_left _ _))
    have hcontinuedEventuallyNe : ∀ᶠ z : ℂ in 𝓝 (x : ℂ),
        continuedExtension z ≠ 0 :=
      (hcontinuedAnalytic (x : ℂ) (Metric.mem_ball_self hr)).continuousAt.eventually_ne
        hcontinuedNe
    have hgood : {z : ℂ | continuedExtension z ≠ 0} ∩
        Metric.ball (x : ℂ) r ∈ 𝓝 (x : ℂ) :=
      inter_mem hcontinuedEventuallyNe (Metric.ball_mem_nhds _ hr)
    obtain ⟨r', hr', hball⟩ := Metric.mem_nhds_iff.mp hgood
    let extension : ℂ → ℂ := fun z ↦
      ((z ^ CompositionDisk.depth tail / continuedExtension z) ^ (ell : ℕ))
    refine ⟨r', hr', extension, ?_, ?_, ?_, ?_⟩
    · exact ((analyticOnNhd_id.pow _).div
        (hcontinuedAnalytic.mono fun z hz ↦ (hball hz).2)
        (fun z hz hzero ↦ (hball hz).1 hzero)).pow _
    · intro z hz
      dsimp only [extension]
      rw [hcontinuedEq ⟨(hball hz.1).2, hz.2⟩]
    · have hextensionLimit : Tendsto extension
          (𝓝[(Metric.ball (x : ℂ) r' ∩ {z : ℂ | 0 < z.im})] (x : ℂ))
          (𝓝 (extension (x : ℂ))) :=
        ((analyticOnNhd_id.pow _).div
          (hcontinuedAnalytic.mono fun z hz ↦ (hball hz).2)
          (fun z hz hzero ↦ (hball hz).1 hzero)).pow _
          (x : ℂ) (Metric.mem_ball_self hr') |>.continuousAt.tendsto.mono_left
            nhdsWithin_le_nhds
      refine hextensionLimit.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      dsimp only [extension]
      rw [hcontinuedEq ⟨(hball hz.1).2, hz.2⟩]
    · have hxt : x - 1 ∈ Set.Ioo 0 δ := ⟨sub_pos.mpr hx, by
        calc
          x - 1 ≤ ρ' := hxρ
          _ ≤ δ / 2 := min_le_right _ _
          _ < δ := half_lt_self hδ⟩
      have hsign := hδsign hxt
      change ((((1 + ((x - 1 : ℝ) : ℂ)) ^ CompositionDisk.depth tail /
        actualUpperBank (head :: tail) (1 + (x - 1))) ^ (ell : ℕ))).im < 0 at hsign
      obtain ⟨η, hη, htrace⟩ := actual_upper_bank_local_trace
        (head :: tail) x r continuedExtension hx hr hcontinuedAnalytic hcontinuedEq
      have hvalue := htrace x (by simpa using hη)
      dsimp only [extension]
      rw [hvalue]
      have hxcomplex : 1 + ((x - 1 : ℝ) : ℂ) = (x : ℂ) := by
        push_cast
        ring
      have hxreal : 1 + (x - 1) = x := by ring
      simpa only [hxcomplex, hxreal] using hsign
  have one_sub_tendsto_slit : Tendsto (fun z : ℂ ↦ 1 - z)
      (𝓝[CompositionContinuation.omega] 1) (𝓝[Complex.slitPlane] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hid : Tendsto (fun z : ℂ ↦ z)
          (𝓝[CompositionContinuation.omega] 1) (𝓝 1) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hone : Tendsto (fun _ : ℂ ↦ (1 : ℂ))
          (𝓝[CompositionContinuation.omega] 1) (𝓝 1) :=
        tendsto_const_nhds
      convert hone.sub hid using 1 <;> norm_num
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact hz

  have composition_nonzero_at_one : ∀ᶠ z : ℂ in
      𝓝[CompositionContinuation.omega] 1,
      CompositionContinuation.continued (head :: tail) z ≠ 0 := by
    filter_upwards [one_sub_tendsto_slit.eventually
      composition_reciprocal_endpoint.1] with z hz
    simpa using hz

  have composition_endpoint_at_one : Tendsto
      (fun z : ℂ ↦ ((z ^ CompositionDisk.depth tail /
        CompositionContinuation.continued (head :: tail) z) ^ (ell : ℕ)))
      (𝓝[CompositionContinuation.omega] 1)
      (𝓝 (if 1 < (head : ℕ) then
        ((CompositionBoundary.zeta head tail : ℂ)⁻¹) ^ (ell : ℕ) else 0)) := by
    have hcomp := composition_reciprocal_endpoint.2.comp one_sub_tendsto_slit
    refine hcomp.congr' (Filter.Eventually.of_forall fun z ↦ ?_)
    dsimp [Function.comp_def]
    have hz : (1 : ℂ) - (1 - z) = z := by ring
    rw [hz]

  have composition_nonzero_radius : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ z ∈ CompositionContinuation.omega, ‖z - 1‖ ≤ ρ →
        CompositionContinuation.continued (head :: tail) z ≠ 0 := by
    change {z : ℂ |
      CompositionContinuation.continued (head :: tail) z ≠ 0} ∈
        𝓝[CompositionContinuation.omega] 1 at composition_nonzero_at_one
    obtain ⟨s, hs, hsubset⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp composition_nonzero_at_one
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    let ρ : ℝ := min (ε / 2) (1 / 2)
    have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
    have hρ1 : ρ < 1 := (min_le_right _ _).trans_lt (by norm_num)
    refine ⟨ρ, hρ0, hρ1, ?_⟩
    intro z hz hzρ
    apply hsubset
    refine ⟨hball ?_, hz⟩
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖z - 1‖ ≤ ρ := hzρ
      _ ≤ ε / 2 := min_le_left _ _
      _ < ε := by linarith

  obtain ⟨ρ₀, hρ₀0, hρ₀1, hnonzero₀⟩ := composition_nonzero_radius
  obtain ⟨ρ₁, hρ₁0, hρ₁1, hupperGerms⟩ :=
    actual_upper_reciprocal_local_extension
  let ρ : ℝ := min ρ₀ ρ₁ / 2
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by
    calc
      ρ ≤ ρ₀ / 2 := by dsimp [ρ]; gcongr; exact min_le_left _ _
      _ < 1 := by linarith
  have hρ_le₀ : ρ ≤ ρ₀ / 2 := by
    dsimp [ρ]
    gcongr
    exact min_le_left _ _
  have hρ_le₁ : ρ ≤ ρ₁ := by
    calc
      ρ ≤ ρ₁ / 2 := by dsimp [ρ]; gcongr; exact min_le_right _ _
      _ ≤ ρ₁ := by linarith
  have hnonzero : ∀ z ∈ CompositionContinuation.omega, ‖z - 1‖ ≤ ρ →
      CompositionContinuation.continued (head :: tail) z ≠ 0 := by
    intro z hz hzρ
    exact hnonzero₀ z hz (hzρ.trans (hρ_le₀.trans (by linarith)))
  let A : ℂ → ℂ := fun z ↦ ((z ^ CompositionDisk.depth tail /
    CompositionContinuation.continued (head :: tail) z) ^ (ell : ℕ))
  let U : Set ℂ := {z | 0 < z.im}
  let B : Set ℂ := {z | ‖z - 1‖ ≤ ρ ∧ 0 ≤ z.im}
  let Bminus : Set ℂ := {z | ‖z - 1‖ ≤ ρ ∧ z.im ≤ 0}
  have upper_mem_omega : ∀ z : ℂ, z ∈ U → z ∈ CompositionContinuation.omega := by
    intro z hz
    change 1 - z ∈ Complex.slitPlane
    rw [Complex.mem_slitPlane_iff]
    right
    simp only [sub_im, one_im, zero_sub, neg_ne_zero]
    exact ne_of_gt hz
  have hAcontinuousBig : ContinuousOn A
      {z | ‖z - 1‖ ≤ ρ₀ ∧ z ∈ CompositionContinuation.omega} := by
    have hcontinued : ContinuousOn
        (CompositionContinuation.continued (head :: tail))
        {z | ‖z - 1‖ ≤ ρ₀ ∧ z ∈ CompositionContinuation.omega} :=
      (continued_analytic (head :: tail)).1.continuousOn.mono fun _ hz ↦ hz.2
    exact ((continuousOn_id.pow _).div hcontinued fun z hz ↦
      hnonzero₀ z hz.2 hz.1).pow _
  have actual_limit_of_omega : ∀ z, z ∈ B → z ∈ CompositionContinuation.omega →
      Tendsto A (𝓝[U] z) (𝓝 (A z)) := by
    intro z hzB hzomega
    have hzBig : z ∈ {w : ℂ | ‖w - 1‖ ≤ ρ₀ ∧
        w ∈ CompositionContinuation.omega} :=
      ⟨hzB.1.trans (hρ_le₀.trans (by linarith)), hzomega⟩
    have hlocal : {w : ℂ | ‖w - 1‖ ≤ ρ₀ ∧
        w ∈ CompositionContinuation.omega} ∈ 𝓝[U] z := by
      apply mem_of_superset
        (inter_mem_nhdsWithin U (Metric.ball_mem_nhds z (half_pos hρ₀0)))
      intro w hw
      refine ⟨?_, upper_mem_omega w hw.1⟩
      have hwz : ‖w - z‖ < ρ₀ / 2 := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hw.2
      apply le_of_lt
      calc
        ‖w - 1‖ ≤ ‖w - z‖ + ‖z - 1‖ := by
          have hdecomp : w - 1 = (w - z) + (z - 1) := by ring
          rw [hdecomp]
          exact norm_add_le _ _
        _ < ρ₀ / 2 + ρ := add_lt_add_of_lt_of_le hwz hzB.1
        _ ≤ ρ₀ := by linarith [hρ_le₀]
    exact (hAcontinuousBig z hzBig).mono_of_mem_nhdsWithin hlocal
  have hBclosure : B ⊆ closure U := by
    intro z hz
    dsimp only [U]
    rw [Complex.closure_setOfPred_lt_im]
    exact hz.2
  have hupperLimits : ∀ z ∈ B, ∃ y, Tendsto A (𝓝[U] z) (𝓝 y) := by
    intro z hzB
    by_cases hzomega : z ∈ CompositionContinuation.omega
    · exact ⟨A z, actual_limit_of_omega z hzB hzomega⟩
    have hzim : z.im = 0 := by
      apply le_antisymm
      · exact le_of_not_gt fun hpos ↦ hzomega (upper_mem_omega z hpos)
      · exact hzB.2
    have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa only [Complex.ofReal_im] using hzim
    have hxge : 1 ≤ z.re := by
      by_contra hx
      apply hzomega
      change 1 - z ∈ Complex.slitPlane
      rw [Complex.mem_slitPlane_iff]
      left
      simp only [sub_re, one_re]
      linarith
    by_cases hx : z.re = 1
    · have hz1 : z = 1 := by
        calc
          z = (z.re : ℂ) := hzreal
          _ = 1 := by rw [hx]; norm_num
      subst z
      refine ⟨if 1 < (head : ℕ) then
        ((CompositionBoundary.zeta head tail : ℂ)⁻¹) ^ (ell : ℕ) else 0, ?_⟩
      exact composition_endpoint_at_one.mono_left
        (nhdsWithin_mono _ upper_mem_omega)
    · have hxgt : 1 < z.re := lt_of_le_of_ne hxge (Ne.symm hx)
      have hxρ : z.re - 1 ≤ ρ := by
        calc
          z.re - 1 = ‖(z.re : ℂ) - 1‖ := by
            rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxge)]
          _ = ‖z - 1‖ :=
            (congrArg (fun w : ℂ ↦ ‖w - 1‖) hzreal).symm
          _ ≤ ρ := hzB.1
      obtain ⟨r, hr, extension, hextension, heq, hlimit, _hsign⟩ :=
        hupperGerms z.re hxgt (hxρ.trans hρ_le₁)
      have hball : Metric.ball (z.re : ℂ) r ∈ 𝓝[U] (z.re : ℂ) :=
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hr)
      rw [nhdsWithin_inter_of_mem hball] at hlimit
      refine ⟨extension (z.re : ℂ), ?_⟩
      change Tendsto A (𝓝[U] (z.re : ℂ)) (𝓝 (extension (z.re : ℂ))) at hlimit
      rw [congrArg (fun w : ℂ ↦ 𝓝[U] w) hzreal]
      exact hlimit
  let upper : ℂ → ℂ := extendFrom U A
  have hupperContinuous : ContinuousOn upper B := by
    exact continuousOn_extendFrom hBclosure hupperLimits
  have hupperAgreement : ∀ z, ‖z - 1‖ ≤ ρ → 0 ≤ z.im →
      z ∈ CompositionContinuation.omega → upper z = A z := by
    intro z hznorm hzim hzomega
    exact extendFrom_eq (hBclosure ⟨hznorm, hzim⟩)
      (actual_limit_of_omega z ⟨hznorm, hzim⟩ hzomega)
  have hupperOne : upper 1 = if 1 < (head : ℕ) then
      ((CompositionBoundary.zeta head tail : ℂ)⁻¹) ^ (ell : ℕ) else 0 := by
    apply extendFrom_eq
    · apply hBclosure
      dsimp only [B]
      exact ⟨by simpa using hρ0.le, by simp⟩
    · exact composition_endpoint_at_one.mono_left
        (nhdsWithin_mono _ upper_mem_omega)
  let lower : ℂ → ℂ := fun z ↦ conj (upper (conj z))
  refine ⟨ρ, hρ0, hρ1, hnonzero, composition_endpoint_at_one,
    upper, lower, hupperContinuous, ?_, ?_, ?_, hupperOne, ?_, ?_, ?_⟩
  · have hconjMaps : MapsTo (fun z : ℂ ↦ conj z) Bminus B := by
      intro z hz
      refine ⟨?_, ?_⟩
      · calc
          ‖conj z - 1‖ = ‖conj (z - 1)‖ := by rw [map_sub, map_one]
          _ = ‖z - 1‖ := Complex.norm_conj _
          _ ≤ ρ := hz.1
      · simpa only [Complex.conj_im, neg_nonneg] using hz.2
    have hupperConj : ContinuousOn (fun z : ℂ ↦ upper (conj z)) Bminus :=
      hupperContinuous.comp' Complex.continuous_conj.continuousOn hconjMaps
    exact Complex.continuous_conj.continuousOn.comp' hupperConj
      (fun _ _ ↦ mem_univ _)
  · intro z hznorm hzim hzomega
    exact hupperAgreement z hznorm hzim hzomega
  · intro z hznorm hzim hzomega
    have hconjNorm : ‖conj z - 1‖ ≤ ρ := by
      calc
        ‖conj z - 1‖ = ‖conj (z - 1)‖ := by rw [map_sub, map_one]
        _ = ‖z - 1‖ := Complex.norm_conj _
        _ ≤ ρ := hznorm
    have hconjIm : 0 ≤ (conj z).im := by
      simpa only [Complex.conj_im, neg_nonneg] using hzim
    have hconjOmega : conj z ∈ CompositionContinuation.omega := by
      change 1 - z ∈ Complex.slitPlane at hzomega
      change 1 - conj z ∈ Complex.slitPlane
      rw [Complex.mem_slitPlane_iff] at hzomega ⊢
      exact hzomega.imp (by simpa) (by simpa)
    have hupper := hupperAgreement (conj z) hconjNorm hconjIm hconjOmega
    have hcontinued := (continued_source head tail).2.2.2 z hzomega
    dsimp only [lower]
    rw [hupper]
    dsimp only [A]
    rw [hcontinued]
    simp
  · dsimp only [lower]
    rw [map_one, hupperOne]
    split <;> simp
  · intro z hznorm hzim
    rfl
  · intro t ht htρ
    obtain ⟨r, hr, extension, _ha, _heq, hlimit, hsign⟩ :=
      hupperGerms (1 + t) (by linarith) (by simpa using htρ.trans hρ_le₁)
    rw [nhdsWithin_inter_of_mem
      (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hr))] at hlimit
    have hlimit' : Tendsto A (𝓝[U] (1 + (t : ℂ)))
        (𝓝 (extension (1 + (t : ℂ)))) := by
      simpa only [A, U, ofReal_add, ofReal_one] using hlimit
    have hnorm : ‖(1 + (t : ℂ)) - 1‖ ≤ ρ := by simpa [abs_of_pos ht] using htρ
    dsimp only [upper]
    rw [extendFrom_eq (hBclosure ⟨hnorm, by simp⟩) hlimit']
    simpa only [ofReal_add, ofReal_one] using hsign
end D5.S3.AnalyticClosure.Polylogarithm.CompositionBanks
