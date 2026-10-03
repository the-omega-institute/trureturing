/- GID: D5/S3/Weil/PrimeNumberTheorem/MediumPNT
   generality: G
   mirror-B: D5/B/S3/Weil/PrimeNumberTheorem/MediumPNT
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Chebyshev psi error decays by an exponential power of logarithm. -/
/-
Source: AlexKontorovich/PrimeNumberTheoremAnd, revision 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01.
Original file: PrimeNumberTheoremAnd/MediumPNT.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0.
Full license and upstream attribution: Library/Weil/primenumbertheoremand2026medium.md.
This file is modified from the cited source.
Retirement: replace this consumed closure with direct references when this
repository's adopted Mathlib revision contains equivalent quantified contracts.
-/
import D5.S3.Weil.PrimeNumberTheorem.PntContourBound
import Batteries.Tactic.Lemma
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Bound
import Mathlib.Algebra.Notation.Support
set_option lang.lemmaCmd true
open Set Function Filter Complex Real MeasureTheory ComplexConjugate Topology
open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev
open scoped ContDiff
local notation (name := mellintransform2) "𝓜" => mellin
local notation "Λ" => vonMangoldt
local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ
set_option maxHeartbeats 800000 in
theorem MediumPNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
  have Smooth1LeOne {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
      (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) {x : ℝ} (xpos : 0 < x) :
      Smooth1 ν ε x ≤ 1 := by
    have hSym {𝕂 : Type} [RCLike 𝕂] (f g : ℝ → 𝕂) {x : ℝ} (xpos : 0 < x) :
        MellinConvolution f g x = MellinConvolution g f x := by
      have hMul (h : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
          ∫ y in Ioi 0, h (y * a) / y = ∫ y in Ioi 0, h y / y := by
        have hh := integral_comp_mul_right_Ioi (fun y ↦ h y / y) 0 ha
        simp only [RCLike.ofReal_mul, zero_mul, eq_inv_smul_iff₀ (ne_of_gt ha)] at hh
        rw [← integral_smul] at hh
        rw [← hh, setIntegral_congr_fun (by simp)]
        intro _ _
        simp only [RCLike.real_smul_eq_coe_mul]
        rw [mul_comm (a : 𝕂), div_mul, mul_div_assoc, div_self ?_, mul_one]
        exact (RCLike.ofReal_ne_zero).mpr <| ne_of_gt ha
      have hInv (h : ℝ → 𝕂) :
          ∫ y in Ioi 0, h (1 / y) / y = ∫ y in Ioi 0, h y / y := by
        have hh := integral_comp_rpow_Ioi (fun y ↦ h y / y) (p := -1) (by simp)
        rw [← hh, setIntegral_congr_fun (by simp)]
        intro y hy
        have : (y : 𝕂) ≠ 0 := (RCLike.ofReal_ne_zero).mpr <| LT.lt.ne' hy
        simp only [abs_neg, abs_one, rpow_neg_one, map_inv₀, div_inv_eq_mul,
          RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]
        ring_nf
        simp [field]
      unfold MellinConvolution
      calc
        _ = ∫ y in Ioi 0, f (y * x) * g (1 / y) / y := ?_
        _ = _ := ?_
      · rw [← hMul (fun y ↦ f y * g (x / y)) xpos]
        simp [div_mul_cancel_right₀ <| ne_of_gt xpos]
      · convert (hInv fun y ↦ f (y * x) * g (1 / y)).symm using 3
        rw [one_div_one_div, mul_comm, mul_comm_div, one_mul]
    have hDiv (h : ℝ → ℝ) {a : ℝ} (ha : 0 < a) :
        ∫ y in Ioi 0, h (a / y) / y = ∫ y in Ioi 0, h y / y := by
      simpa only [MellinConvolution, one_mul, mul_one, RCLike.ofReal_real_eq_id, id_eq] using
        (hSym (𝕂 := ℝ) (fun _ : ℝ ↦ (1 : ℝ)) h ha)
    have hPow (h : ℝ → ℝ) {p : ℝ} (hp : p ≠ 0) :
        ∫ y in Ioi 0, |p| * h (y ^ p) / y = ∫ y in Ioi 0, h y / y := by
      rw [← integral_comp_rpow_Ioi (fun y ↦ h y / y) hp,
        setIntegral_congr_fun (by simp)]
      intro y hy
      have ypos : 0 < y := mem_Ioi.mp hy
      simp only [rpow_sub_one ypos.ne', smul_eq_mul]
      field_simp
    have hMass : ∫ y in Ioi 0, ν ((x / y) ^ (1 / ε)) / ε / y = 1 := by
      calc
        _ = ∫ y in Ioi 0, (ν (y ^ (1 / ε)) / ε) / y := ?_
        _ = ∫ y in Ioi 0, ν y / y := ?_
        _ = 1 := mass_one
      · have hh := hDiv (fun y ↦ ν ((x / y) ^ (1 / ε)) / ε) xpos
        convert! hh.symm using 1
        congr; funext y; congr; field_simp [mul_comm]
      · have hh := hPow (fun y ↦ ν y) (one_div_ne_zero εpos.ne')
        rw [← hh, abs_of_pos <| one_div_pos.mpr εpos]
        field_simp
    unfold Smooth1 MellinConvolution DeltaSpike
    calc
      _ = ∫ (y : ℝ) in Ioi 0,
          (fun y ↦ if y ∈ Ioc 0 1 then 1 else 0) y * (ν ((x / y) ^ (1 / ε)) / ε / y) := ?_
      _ ≤ ∫ (y : ℝ) in Ioi 0, (ν ((x / y) ^ (1 / ε)) / ε) / y := ?_
      _ = 1 := hMass
    · rw [setIntegral_congr_fun (by simp)]
      simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq, mem_Ioc]
      intro y hy; aesop
    · refine setIntegral_mono_on ?_ (integrable_of_integral_eq_one hMass) (by simp) ?_
      · refine integrable_of_integral_eq_one hMass |>.bdd_mul ?_
          (ae_of_all _ <| by aesop)
        have : (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) =
            indicator (Ioc 0 1) (1 : ℝ → ℝ) := by
          aesop
        simp only [mem_Ioc, this, measurableSet_Ioc, aestronglyMeasurable_indicator_iff]
        exact aestronglyMeasurable_one
      · simp only [ite_mul, one_mul, zero_mul]
        intro y hy
        by_cases h : y ≤ 1
        · aesop
        field_simp
        simp only [mem_Ioc, h, and_false, ↓reduceIte, one_div, mul_zero]
        simp only [mem_Ioi] at hy
        apply div_nonneg
        · apply νnonneg; exact rpow_pos_of_pos (div_pos xpos <| mem_Ioi.mp hy) _
        · positivity
  have SmoothExistence :
      ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
    suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
        ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
      obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
      let c := (∫ x in Ici 0, ν x / x)
      use fun y ↦ ν y / c
      refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
      · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
        convert hνsupp
      · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
    have hBump : ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
        Set.indicator (Set.Icc 1 (3 / 2)) 1 ≤ Ψ ∧
        Ψ ≤ Set.indicator (Set.Ioo (1 / 2) 2) 1 ∧
        (Function.support Ψ = Set.Ioo (1 / 2) 2) := by
      have hUrysohn := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
        (modelWithCornersSelf ℝ ℝ)
        (s := Set.Iic (1 / 2 : ℝ) ∪ Set.Ici 2)
        (t := Set.Icc 1 (3 / 2 : ℝ))
        (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
        (by
          simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
            Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
            and_imp, imp_false, not_le, Set.mem_Ici]
          constructor <;> intros <;> linarith)
      obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := hUrysohn
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
      use Ψ
      simp only [range_subset_iff, mem_Icc] at hΨrange
      refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
      · apply HasCompactSupport.of_support_subset_isCompact
          (K := Set.Icc (1 / 2 : ℝ) 2) isCompact_Icc
        simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
        bound
      · apply Set.indicator_le'
        · intro x hx
          rw [hΨ1 x |>.mp, Pi.one_apply]
          simpa using hx
        · exact fun x _ ↦ (hΨrange x).1
      · intro x
        apply Set.le_indicator_apply
        · exact fun _ ↦ (hΨrange x).2
        · intro hx
          rw [← hΨ0 x |>.mp]
          simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
      · ext x
        simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]
    obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := hBump
    use ν, hνContDiff
    unfold indicator at hν0 hν1
    simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
    simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
    split_ands
    · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
    · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
    · rw [integral_pos_iff_support_of_nonneg]
      · have hSupportId : Function.support (fun a : ℝ => a) = {0}ᶜ := by
          ext x
          simp
        simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
          hνSupport, hSupportId]
        have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
          ext x
          simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
          bound
        simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
        linarith
      · simp_rw [Pi.le_def, Pi.zero_apply]
        intro y
        by_cases h : y ∈ Function.support ν
        · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
          rw [hνSupport, mem_Ioo] at h
          linarith [h.left]
        · simp only [Function.mem_support, ne_eq, not_not] at h
          simp [h]
      · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
          rw [Function.support_div, hνSupport]
          exact (inter_subset_left).trans Ioo_subset_Icc_self
        apply (integrableOn_iff_integrable_of_support_subset this).mp
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
        simp only [mem_Icc, ne_eq, and_imp, id_eq]
        intros; linarith
  have x_ε_to_inf (c : ℝ) {B : ℝ} (B_le : B < 1) : Tendsto
      (fun x ↦ x * Real.exp (-c * (Real.log x) ^ B)) atTop atTop := by
    have coeff_to_zero {B : ℝ} (B_le : B < 1) :
        Tendsto (fun x ↦ Real.log x ^ (B - 1)) atTop (𝓝 0) := by
      have B_minus_1_neg : B - 1 < 0 := by linarith
      rw [← Real.zero_rpow (ne_of_lt B_minus_1_neg),
        zero_rpow (ne_of_lt B_minus_1_neg)]
      have one_minus_B_pos : 0 < 1 - B := by linarith
      rw [show B - 1 = -(1 - B) by ring]
      have : ∀ᶠ (x : ℝ) in atTop, Real.log x ^ (-(1 - B)) = (Real.log x ^ ((1 - B)))⁻¹ := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
        apply Real.rpow_neg
        exact Real.log_nonneg hx
      rw [tendsto_congr' this]
      apply tendsto_inv_atTop_zero.comp
      apply (tendsto_rpow_atTop one_minus_B_pos).comp
      exact tendsto_log_atTop
    have log_sub_log_pow_inf (c : ℝ) {B : ℝ} (B_le : B < 1) :
        Tendsto (fun (x : ℝ) ↦ Real.log x - c * Real.log x ^ B) atTop atTop := by
      have factor_form : ∀ x > 1, Real.log x - c * Real.log x ^ B =
          Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
        intro x hx
        ring_nf
        congr! 1
        rw [mul_assoc, mul_comm (Real.log x), mul_assoc]
        congr! 1
        have log_pos : 0 < Real.log x := Real.log_pos hx
        rw [(by simp : Real.log x ^ (-1 + B) * Real.log x =
          Real.log x ^ (-1 + B) * (Real.log x) ^ (1 : ℝ))]
        rw [← Real.rpow_add log_pos]
        ring_nf
      have coeff_to_one : Tendsto (fun x ↦ 1 - c * Real.log x ^ (B - 1)) atTop (𝓝 1) := by
        specialize coeff_to_zero B_le
        apply Tendsto.const_mul c at coeff_to_zero
        convert (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).sub coeff_to_zero
        ring
      have eventually_factored : ∀ᶠ x in atTop, Real.log x - c * Real.log x ^ B =
      Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
        filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
        exact factor_form x hx
      rw [tendsto_congr' eventually_factored]
      apply Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) tendsto_log_atTop  coeff_to_one
    have x_εx_eq (c B : ℝ) : ∀ᶠ (x : ℝ) in atTop, x * rexp (-c * Real.log x ^ B) =
          rexp (Real.log x - c * Real.log x ^ B) := by
      filter_upwards [eventually_gt_atTop 0] with x hx_pos
      conv =>
        enter [1, 1]
        rw [(Real.exp_log hx_pos).symm]
      rw [← Real.exp_add]
      ring_nf
    rw [tendsto_congr' (x_εx_eq c B)]
    exact tendsto_exp_atTop.comp (log_sub_log_pow_inf c B_le)
  have Smooth1Nonneg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x) {ε x : ℝ}
      (xpos : 0 < x) (εpos : 0 < ε) : 0 ≤ Smooth1 ν ε x := by
    unfold Smooth1 MellinConvolution DeltaSpike
    apply MeasureTheory.setIntegral_nonneg
    · exact measurableSet_Ioi
    · intro y hy
      have ypos : 0 < y := mem_Ioi.mp hy
      have hν : 0 ≤ ν ((x / y) ^ (1 / ε)) :=
        νnonneg _ (rpow_pos_of_pos (div_pos xpos ypos) _)
      by_cases h : y ≤ 1
      · simpa [ypos, h] using (div_nonneg (div_nonneg hν εpos.le) ypos.le)
      · simp [ypos, h]
  have smoothedChebyshevIntegrand_conj
      {SmoothingF : ℝ → ℝ} {ε X : ℝ} (Xpos : 0 < X) (s : ℂ) :
      SmoothedChebyshevIntegrand SmoothingF ε X (conj s) =
        conj (SmoothedChebyshevIntegrand SmoothingF ε X s) := by
    unfold SmoothedChebyshevIntegrand
    simp only [map_mul, map_div₀, map_neg]
    congr
    · exact deriv_riemannZeta_conj s
    · exact riemannZeta_conj s
    · unfold mellin
      rw [← integral_conj]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x xpos
      simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
      congr
      nth_rw 1 [← map_one conj]
      rw [← map_sub, Complex.cpow_conj, Complex.conj_ofReal]
      rw [Complex.arg_ofReal_of_nonneg xpos.le]
      exact Real.pi_ne_zero.symm
    · rw [Complex.cpow_conj, Complex.conj_ofReal]
      rw [Complex.arg_ofReal_of_nonneg Xpos.le]
      exact Real.pi_ne_zero.symm
  have Smooth1MellinDifferentiable {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
      (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
      (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
      {s : ℂ} (hs : 0 < s.re) :
      DifferentiableAt ℂ (𝓜 (fun x ↦ (Smooth1 Ψ ε x : ℂ))) s := by
    apply mellin_differentiableAt_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
    · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
      apply continuousOn_of_forall_continuousAt
      exact fun x hx ↦ Smooth1ContinuousAt diffΨ Ψnonneg suppΨ hε.1 hx |>.ofReal
    · rw [Asymptotics.isBigO_iff]
      use 1
      obtain ⟨c, cpos, ceq, hc⟩ := Smooth1Properties_above suppΨ
      filter_upwards [eventually_ge_atTop (1 + c * ε)] with x hx
      rw [hc _ _ hε hx]
      simp only [ofReal_zero, norm_zero, neg_mul, one_mul, norm_eq_abs, abs_exp]
      bound
    · rw [Asymptotics.isBigO_iff]
      use 1
      filter_upwards [eventually_mem_nhdsWithin] with x hx
      simp only [norm_real, norm_eq_abs, neg_zero, rpow_zero, one_mem, CStarRing.norm_of_mem_unitary,
        mul_one]
      rw [_root_.abs_of_nonneg <| Smooth1Nonneg Ψnonneg hx hε.1]
      exact Smooth1LeOne Ψnonneg mass_one hε.1 hx
  have ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have ContDiff1ν : ContDiff ℝ 1 ν := by
    exact ContDiffν.of_le (by simp)
  have ν_nonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have ν_massOne : ∫ x in Ioi 0, ν x / x = 1 := by
    rwa [← integral_Ici_eq_integral_Ioi]
  clear ContDiffν ν_nonneg'  ν_massOne'
  obtain ⟨c_close, c_close_pos, h_close⟩ :=
    SmoothedChebyshevClose ContDiff1ν ν_supp ν_nonneg ν_massOne
  have MellinOfDeltaSpikeAt1_asymp {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
      (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
      (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) :
      (fun (ε : ℝ) ↦ (𝓜 (fun x ↦ (ν x : ℂ)) ε) - 1) =O[𝓝[>]0] id := by
    have diff : DifferentiableWithinAt ℝ
        (fun (ε : ℝ) ↦ 𝓜 (fun x ↦ (ν x : ℂ)) ε - 1) (Ioi 0) 0 := by
      apply DifferentiableAt.differentiableWithinAt
      simp only [(differentiableAt_const _).fun_sub_iff_left]
      refine DifferentiableAt.comp_ofReal ?_
      refine mellin_differentiableAt_of_isBigO_rpow (a := 1) (b := -1) ?_ ?_ (by simp) ?_ (by simp)
      · apply (Continuous.continuousOn ?_).locallyIntegrableOn (by simp)
        have := diffν.continuous; continuity
      · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
        refine Eventually.isBigO ?_
        filter_upwards [Ioi_mem_atTop (2 : ℝ)] with c hc
        have hzero : ν c = 0 :=
          Function.support_subset_iff'.mp suppν c
            (fun h ↦ by linarith [mem_Icc.mp h, mem_Ioi.mp hc])
        exact norm_le_zero_iff.mpr (by simp [hzero])
      · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
        refine Eventually.isBigO ?_
        filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with c hc
        have hzero : ν c = 0 :=
          Function.support_subset_iff'.mp suppν c
            (fun h ↦ by linarith [mem_Icc.mp h, (mem_Ioo.mp hc).2])
        exact norm_le_zero_iff.mpr (by simp [hzero])
    have := ofReal_zero ▸ diff.isBigO_sub
    simp only [sub_sub_sub_cancel_right, sub_zero] at this
    convert! this using 1
    simp only [mellin, zero_sub, cpow_neg_one, smul_eq_mul]
    funext ε
    congr 1
    symm
    calc (∫ (t : ℝ) in Ioi 0, (↑t)⁻¹ * ↑(ν t) : ℂ)
        = ∫ (t : ℝ) in Ioi 0, ((ν t / t : ℝ) : ℂ) :=
          integral_congr_ae (Filter.Eventually.of_forall fun t => by push_cast; ring)
      _ = ((∫ t in Ioi 0, ν t / t : ℝ) : ℂ) := integral_ofReal
      _ = 1 := by rw [mass_one, ofReal_one]
  have hMainExplicit : ∃ ε₀ c : ℝ, 0 < ε₀ ∧ 0 < c ∧
      ∀ ε ∈ Ioo 0 ε₀,
        ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1‖ ≤ c * ε := by
    have h : (fun ε ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1) =O[𝓝[>]0] id := by
      have h := MellinOfDeltaSpikeAt1_asymp ContDiff1ν ν_supp ν_massOne
      rw [Asymptotics.isBigO_iff] at h ⊢
      obtain ⟨c, hc⟩ := h
      use c
      filter_upwards [hc, Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1)] with ε hε hε'
      rw [MellinOfSmooth1a ContDiff1ν ν_supp hε'.1 (s := 1) (by norm_num)]
      simp only [inv_one, mul_one, one_mul, id_eq, Real.norm_eq_abs]
      exact hε
    rw [Asymptotics.isBigO_iff'] at h
    rcases h with ⟨c, cpos, hc⟩
    unfold Filter.Eventually at hc
    rw [mem_nhdsGT_iff_exists_Ioo_subset] at hc
    rcases hc with ⟨ε₀, ε₀pos, h⟩
    refine ⟨ε₀, c, ε₀pos, cpos, fun ε hε ↦ ?_⟩
    specialize h hε
    rw [mem_setOf_eq, id_eq, norm_of_nonneg hε.1.le] at h
    exact h
  obtain ⟨ε_main, C_main, ε_main_pos, C_main_pos, h_main⟩ := hMainExplicit
  have hZetaJoint : ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧
      LogDerivZetaHasBound A C ∧ ∀ (T : ℝ) (_ : 3 ≤ T),
      HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
        ((Icc ((1 : ℝ) - A / Real.log T ^ 9) 2 ×ℂ Icc (-T) T) \ {1}) := by
    obtain ⟨A₁, A₁_in, C, C_pos, zeta_bnd⟩ := LogDerivZetaBndUnif
    obtain ⟨A₂, A₂_in, holo⟩ := LogDerivZetaHolcLargeT
    refine ⟨min A₁ A₂, C, C_pos, ?_, ?_, ?_⟩
    · exact ⟨lt_min A₁_in.1 A₂_in.1, le_trans (min_le_left _ _) A₁_in.2⟩
    · intro σ T hT hσ
      apply zeta_bnd _ _ hT
      apply mem_Ici.mpr (le_trans _ hσ)
      gcongr
      · bound
      · apply min_le_left
    · intro T hT
      apply (holo _ hT).mono
      intro s hs
      simp only [Set.mem_sdiff, mem_singleton_iff, mem_reProdIm] at hs ⊢
      refine ⟨?_, hs.2⟩
      refine ⟨?_, hs.1.2⟩
      refine ⟨?_, hs.1.1.2⟩
      apply le_trans _ hs.1.1.1
      gcongr
      · bound
      · apply min_le_right
  obtain ⟨A, C_bnd, C_bnd_pos, A_in_Ioc, zeta_bnd, holo1⟩ := hZetaJoint
  obtain ⟨σ₂', σ₂'_lt_one, holo2'⟩ := LogDerivZetaHolcSmallT
  let σ₂ : ℝ := max σ₂' (1 / 2)
  have σ₂_pos : 0 < σ₂ := by bound
  have σ₂_lt_one : σ₂ < 1 := by bound
  have holo2 : HolomorphicOn (fun s ↦ ζ' s / ζ s) (uIcc σ₂ 2 ×ℂ uIcc (-3) 3 \ {1}) := by
    apply holo2'.mono
    intro s hs
    simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, Set.mem_sdiff, mem_reProdIm, mem_Icc,
      mem_singleton_iff] at hs ⊢
    refine ⟨?_, hs.2⟩
    refine ⟨?_, hs.1.2⟩
    rcases hs.1.1 with ⟨left, right⟩
    constructor
    · apply le_trans _ left
      apply min_le_min_right
      apply le_max_left
    · rw [max_eq_right (by linarith)] at right ⊢
      exact right
  clear holo2' σ₂'_lt_one
  obtain ⟨c₁, c₁pos, hc₁⟩ := I1Bound ν_supp ContDiff1ν ν_nonneg ν_massOne
  obtain ⟨c₂, c₂pos, hc₂⟩ := I2Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₃, c₃pos, hc₃⟩ := I3Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₅, c₅pos, hContour⟩ :=
    SmoothedChebyshevContourBound ν_supp ContDiff1ν ν_nonneg ν_massOne
      (show LogDerivZetaIsHoloSmall σ₂ from holo2) ⟨σ₂_pos, σ₂_lt_one⟩
  let c₇ := c₃
  have c₇pos : 0 < c₇ := c₃pos
  let c₈ := c₂
  have c₈pos : 0 < c₈ := c₂pos
  let c₉ := c₁
  have c₉pos : 0 < c₉ := c₁pos
  obtain ⟨c₄, c₄pos, Tlb₄, Tlb₄bnd, hc₄⟩ := I4Bound ν_supp ContDiff1ν
    holo2 ⟨σ₂_pos, σ₂_lt_one⟩ A_in_Ioc
  let c₆ := c₄
  have c₆pos : 0 ≤ c₆ := c₄pos
  let Tlb₆ := Tlb₄
  have Tlb₆bnd : 3 < Tlb₆ := Tlb₄bnd
  let C' := c_close + C_main
  let C'' := c₁ + c₂ + c₈ + c₉
  let C''' := c₃ + c₄ + c₆ + c₇

  let c : ℝ := A ^ ((1 : ℝ) / 10) / 4
  have cpos : 0 < c := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, lt_sup_iff,
      inv_pos, Nat.ofNat_pos, or_true, sup_lt_iff, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, σ₂, c]
    obtain ⟨left, right⟩ := A_in_Ioc
    positivity
  refine ⟨c, cpos, ?_⟩
  rw [Asymptotics.isBigO_iff]
  let C : ℝ := C' + C'' + C''' + c₅
  refine ⟨C, ?_⟩

  let c_εx : ℝ := A ^ ((1 : ℝ) / 10) / 2
  have c_εx_pos : 0 < c_εx := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, lt_sup_iff,
      inv_pos, Nat.ofNat_pos, or_true, sup_lt_iff, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, σ₂, c, c_εx]
  let c_Tx : ℝ := A ^ ((1 : ℝ) / 10)
  have c_Tx_pos : 0 < c_Tx := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, lt_sup_iff,
      inv_pos, Nat.ofNat_pos, or_true, sup_lt_iff, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, σ₂, c, c_εx, c_Tx]

  let εx := (fun x ↦ Real.exp (-c_εx * (Real.log x) ^ ((1 : ℝ) / 10)))
  let Tx := (fun x ↦ Real.exp (c_Tx * (Real.log x) ^ ((1 : ℝ) / 10)))

  have Tx_to_inf : Tendsto Tx atTop atTop := by
    unfold Tx
    apply tendsto_exp_atTop.comp
    apply Tendsto.pos_mul_atTop c_Tx_pos tendsto_const_nhds
    exact (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 10)).comp Real.tendsto_log_atTop

  have ex_to_zero : Tendsto εx atTop (𝓝 0) := by
    unfold εx
    apply Real.tendsto_exp_atBot.comp
    have this (x) : -c_εx * Real.log x ^ ((1 : ℝ) / 10) = -(c_εx * Real.log x ^ ((1 : ℝ) / 10)) := by
      ring
    simp_rw [this]
    rw [tendsto_neg_atBot_iff]
    apply Tendsto.const_mul_atTop c_εx_pos
    apply (tendsto_rpow_atTop (by norm_num)).comp
    exact tendsto_log_atTop

  have eventually_εx_lt_one : ∀ᶠ (x : ℝ) in atTop, εx x < 1 := by
    apply (tendsto_order.mp ex_to_zero).2
    norm_num

  have eventually_2_lt : ∀ᶠ (x : ℝ) in atTop, 2 < x * εx x := by
    have := x_ε_to_inf c_εx (by norm_num : (1 : ℝ) / 10 < 1)
    exact this.eventually_gt_atTop 2

  have eventually_T_gt_3 : ∀ᶠ (x : ℝ) in atTop, 3 < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop 3

  have eventually_T_gt_Tlb₄ : ∀ᶠ (x : ℝ) in atTop, Tlb₄ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _
  have eventually_T_gt_Tlb₆ : ∀ᶠ (x : ℝ) in atTop, Tlb₆ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _

  have eventually_σ₂_lt_σ₁ : ∀ᶠ (x : ℝ) in atTop, σ₂ < 1 - A / (Real.log (Tx x)) ^ 9 := by
    apply (tendsto_order.mp ?_).1
    · exact σ₂_lt_one
    have := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9)).comp
      (tendsto_log_atTop.comp Tx_to_inf))
    have := Tendsto.const_mul (b := A) this
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub this using 2
    · simp only [rpow_ofNat, comp_apply, div_eq_mul_inv]
    · simp

  have eventually_ε_lt_ε_main : ∀ᶠ (x : ℝ) in atTop, εx x < ε_main := by
    apply (tendsto_order.mp ex_to_zero).2
    assumption

  have event_logX_ge : ∀ᶠ (x : ℝ) in atTop, 1 ≤ Real.log x := by
    apply Real.tendsto_log_atTop.eventually_ge_atTop

  have event_1_aux_1 {const1 const2 : ℝ} (const1pos : 0 < const1) (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp 0 := by
      have := ((isLittleO_log_rpow_atTop const2pos).bound const1pos)
      have : ∀ᶠ (x : ℝ) in atTop, Real.log (Real.log x) ≤
          const1 * (Real.log x) ^ const2 := by
        have := tendsto_log_atTop.eventually this
        filter_upwards [this, eventually_gt_atTop 10] with x hx x_gt
        convert hx using 1
        · rw [Real.norm_of_nonneg]
          exact Real.log_nonneg (logt_gt_one (by linarith)).le
        · congr! 1
          rw [Real.norm_of_nonneg]
          apply Real.rpow_nonneg
          apply Real.log_nonneg
          linarith
      have loglogx :  ∀ᶠ (x : ℝ) in atTop,
          Real.log x = rexp (Real.log (Real.log x)) := by
        filter_upwards [eventually_gt_atTop 3] with x hx
        rw [Real.exp_log]
        apply Real.log_pos
        linarith
      filter_upwards [loglogx, this] with x loglogx hx
      conv =>
        enter [1, 2]
        rw [loglogx]
      rw [← Real.exp_add]
      apply Real.exp_monotone
      grw [hx]
      simp

  have event_1_aux {const1 const1' const2 : ℝ} (const1bnds : const1' < const1)
    (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp (-const1' * Real.log x ^ const2) := by
      have : 0 < const1 - const1' := by linarith
      filter_upwards [event_1_aux_1 this const2pos] with x hx
      have : rexp (-const1 * Real.log x ^ const2) * Real.log x
        = rexp (-(const1') * Real.log x ^ const2)
          * rexp (-(const1 - const1') * Real.log x ^ const2) * Real.log x := by
          congr! 1
          rw [← Real.exp_add]
          congr! 1
          ring
      rw [this,
        mul_assoc]

      grw [hx]
      simp

  have event_1 : ∀ᶠ (x : ℝ) in atTop, C' * (εx x) * x * Real.log x ≤
      C' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 10)) := by
    unfold c εx c_εx
    have const1bnd : (A ^ ((1 : ℝ) / 10) / 4) < (A ^ ((1 : ℝ) / 10) / 2) := by
        linarith
    have const2bnd : (0 : ℝ) < 1 / 10 := by norm_num
    have this (x) :
      C' * rexp (-(A ^ ((1 : ℝ) / 10) / 2) * Real.log x ^ ((1 : ℝ) / 10)) * x * Real.log x =
      C' * x * (rexp (-(A ^ ((1 : ℝ) / 10) / 2) * Real.log x ^ ((1 : ℝ) / 10)) * Real.log x) := by ring
    simp_rw [this]
    filter_upwards [event_1_aux const1bnd const2bnd, eventually_gt_atTop 3] with x x_bnd x_gt
    grw [x_bnd]

  have event_2 : ∀ᶠ (x : ℝ) in atTop, C'' * x * Real.log x / (εx x * Tx x) ≤
      C'' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 10)) := by
    unfold c εx c_εx Tx c_Tx
    set const2 : ℝ := 1 / 10
    have const2bnd : 0 < const2 := by norm_num
    set const1 := (A ^ const2 / 2)
    set const1' := (A ^ const2 / 4)
    have this (x) : -(-const1 * Real.log x ^ const2 + A ^ const2 * Real.log x ^ const2) =
      -(A ^ const2 - const1) * Real.log x ^ const2 := by ring
    simp_rw [← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, this]
    have const1bnd : const1' < (A ^ const2 - const1) := by
      unfold const1' const1
      linarith
    filter_upwards [event_1_aux const1bnd const2bnd, eventually_gt_atTop 3] with x x_bnd x_gt
    rw [mul_assoc]
    conv =>
      enter [1, 2]
      rw [mul_comm]
    grw [x_bnd]

  have event_3_aux {const1 const1' const2 : ℝ} (const2_eq : const2 = 1 / 10)
    (const1_eq : const1 = (A ^ const2 / 2)) (const1'_eq : const1' = (A ^ const2 / 4)) :
    ∀ᶠ (x : ℝ) in atTop,
      x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ (9 : ℝ)) *
      rexp (-(-const1 * Real.log x ^ const2)) ≤
      rexp (-const1' * Real.log x ^ const2) := by
    have : ∀ᶠ (x : ℝ) in atTop, x = rexp (Real.log x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.exp_log hx]
    filter_upwards [this, eventually_gt_atTop 3] with x hx x_gt_3
    have logxpos : 0 < Real.log x := by apply Real.log_pos; linarith
    conv =>
      enter [1, 1, 1]
      rw [hx]
    rw [← Real.exp_mul,
      Real.log_exp]
    rw [Real.mul_rpow]
    · have {y : ℝ} (ypos : 0 < y) : y / (y ^ const2) ^ (9 : ℝ) = y ^ const2 := by
        rw [← Real.rpow_mul ypos.le,
          div_eq_mul_inv]
        rw [← Real.rpow_neg ypos.le]
        conv =>
          enter [1, 1]
          rw [← Real.rpow_one y]
        rw [← Real.rpow_add ypos,
          (by linarith : 1 + -(const2 * 9) = const2)]
      rw [div_mul_eq_div_div,
        neg_div]
      rw [this (A_in_Ioc.1)]
      rw [mul_div]
      conv =>
        enter [1, 1, 1, 1]
        rw [mul_comm]
      rw [← mul_div]
      rw [this (y := Real.log x) logxpos]
      rw [← Real.exp_add]
      apply Real.exp_monotone
      have : -A ^ const2 * Real.log x ^ const2 + -(-const1 * Real.log x ^ const2)
       = (-(A ^ const2 - const1) * Real.log x ^ const2) := by ring
      rw [this]
      gcongr
      rw [const1'_eq, const1_eq]
      have : 0 ≤ A ^ const2 := by
        apply Real.rpow_nonneg A_in_Ioc.1.le
      linarith
    · rw [const2_eq]
      positivity
    · apply Real.rpow_nonneg
      apply Real.log_nonneg
      linarith
  have event_3 : ∀ᶠ (x : ℝ) in atTop, C''' * x * x ^ (-A / Real.log (Tx x) ^ 9) / (εx x) ≤
      C''' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 10)) := by
    unfold c Tx c_Tx εx c_εx
    set const2 : ℝ := 1 / 10
    have const2eq : const2 = 1 / 10 := rfl
    set const1 := (A ^ const2 / 2)
    have const1eq : const1 = (A ^ const2 / 2) := rfl
    set const1' := (A ^ const2 / 4)
    have const1'eq : const1' = (A ^ const2 / 4) := rfl
    conv =>
      enter [1, x, 1]
      rw [div_eq_mul_inv, ← Real.exp_neg]
    filter_upwards [event_3_aux const2eq const1eq const1'eq,
      eventually_gt_atTop 3] with x x_bnd x_gt
    have this (x) : C''' * x * x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ 9)
        * rexp (-(-const1 * Real.log x ^ const2))
      = C''' * x * (x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ (9 : ℝ))
        * rexp (-(-const1 * Real.log x ^ const2))) := by
      norm_cast
      ring
    rw [this]
    grw [x_bnd]
  have event_4_aux4 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      Tendsto (fun x ↦ c' * Real.log x ^ pow2) atTop (𝓝 0) := by
    rw [← mul_zero c']
    apply Tendsto.const_mul
    have := tendsto_rpow_neg_atTop (y := -pow2) (by linarith)
    rw [neg_neg] at this
    apply this.comp
    exact Real.tendsto_log_atTop
  have event_4_aux3 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      ∀ᶠ (x : ℝ) in atTop, c' * (Real.log x) ^ pow2 < c := by
    apply (event_4_aux4 pow2_neg cpos c').eventually_lt_const
    exact cpos
  have event_4_aux2 {c1 : ℝ} (c1pos : 0 < c1) (c2 : ℝ) {pow1 : ℝ} (pow1_lt : pow1 < 1) :
      ∀ᶠ (x : ℝ) in atTop, 0 ≤ Real.log x * (c1 - c2 * (Real.log x) ^ (pow1 - 1)) := by
    filter_upwards [eventually_gt_atTop 3 , event_4_aux3 (by linarith : pow1 - 1 < 0)
      (by linarith : 0 < c1 / 2) c2] with x x_gt hx
    have : 0 ≤ Real.log x := by
      apply Real.log_nonneg
      linarith
    apply mul_nonneg this
    linarith
  have event_4_aux1 {const1 : ℝ} (const1_lt : const1 < 1) (const2 const3 : ℝ)
      {pow1 : ℝ} (pow1_lt : pow1 < 1) : ∀ᶠ (x : ℝ) in atTop,
      const1 * Real.log x + const2 * Real.log x ^ pow1
        ≤ Real.log x - const3 * Real.log x ^ pow1 := by
    filter_upwards [event_4_aux2 (by linarith : 0 < 1 - const1) (const2 + const3) pow1_lt,
      eventually_gt_atTop 3] with x hx x_gt
    rw [← sub_nonneg]
    have :
      Real.log x - const3 * Real.log x ^ pow1 - (const1 * Real.log x + const2 * Real.log x ^ pow1)
      = (1 - const1) * Real.log x - (const2 + const3) * Real.log x ^ pow1 := by ring
    rw [this]
    convert hx using 1
    ring_nf
    congr! 1
    · have : Real.log x * const2 * Real.log x ^ (-1 + pow1)
          = const2 * Real.log x ^ pow1 := by
        rw [mul_assoc, mul_comm, mul_assoc]
        congr! 1
        conv =>
          enter [1, 2]
          rw [← Real.rpow_one (Real.log x)]
        rw [← Real.rpow_add (Real.log_pos (by linarith))]
        ring_nf
      rw [this]
    have : Real.log x * const3 * Real.log x ^ (-1 + pow1)
        = const3 * Real.log x ^ pow1 := by
      rw [mul_assoc, mul_comm, mul_assoc]
      congr! 1
      conv =>
        enter [1, 2]
        rw [← Real.rpow_one (Real.log x)]
      rw [← Real.rpow_add (Real.log_pos (by linarith))]
      ring_nf
    rw [this]
  have event_4_aux : ∀ᶠ (x : ℝ) in atTop,
      c₅ * rexp (σ₂ * Real.log x + (A ^ ((1 : ℝ) / 10) / 2) * Real.log x ^ ((1 : ℝ) / 10)) ≤
      c₅ * rexp (Real.log x - (A ^ ((1 : ℝ) / 10) / 4) * Real.log x ^ ((1 : ℝ) / 10)) := by
    filter_upwards [eventually_gt_atTop 3, event_4_aux1 σ₂_lt_one (A ^ ((1 : ℝ) / 10) / 2)
      (A ^ ((1 : ℝ) / 10) / 4) (by norm_num : (1 : ℝ) / 10 < 1)] with x x_gt hx
    rw [mul_le_mul_iff_right₀ c₅pos]
    apply Real.exp_monotone
    convert hx

  have event_4 : ∀ᶠ (x : ℝ) in atTop, c₅ * x ^ σ₂ / (εx x) ≤
      c₅ * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 10)) := by
    unfold εx c_εx c
    filter_upwards [event_4_aux, eventually_gt_atTop 0] with x hx xpos
    convert hx using 1
    · rw [← mul_div]
      congr! 1
      rw [div_eq_mul_inv, ← Real.exp_neg]
      conv =>
        enter [1, 1, 1]
        rw [← Real.exp_log xpos]
      rw [← exp_mul, ← Real.exp_add]
      ring_nf

    · rw [mul_assoc]
      congr! 1
      conv =>
        enter [1, 1]
        rw [← Real.exp_log xpos]
      rw [← Real.exp_add]
      ring_nf

  filter_upwards [eventually_gt_atTop 3, eventually_εx_lt_one, eventually_2_lt,
    eventually_T_gt_3, eventually_T_gt_Tlb₄, eventually_T_gt_Tlb₆,
      eventually_σ₂_lt_σ₁, eventually_ε_lt_ε_main, event_logX_ge, event_1, event_2,
      event_3, event_4] with X X_gt_3 ε_lt_one ε_X T_gt_3 T_gt_Tlb₄ T_gt_Tlb₆
      σ₂_lt_σ₁ ε_lt_ε_main logX_ge event_1 event_2 event_3 event_4

  clear eventually_εx_lt_one eventually_2_lt eventually_T_gt_3 eventually_T_gt_Tlb₄
    eventually_T_gt_Tlb₆ eventually_σ₂_lt_σ₁ eventually_ε_lt_ε_main event_logX_ge zeta_bnd

  let ε : ℝ := εx X
  have ε_pos : 0 < ε := by positivity
  specialize h_close X X_gt_3 ε ε_pos ε_lt_one ε_X
  let ψ_ε_of_X := SmoothedChebyshev ν ε X

  let T : ℝ := Tx X
  specialize holo1 T T_gt_3.le
  let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
  have σ₁pos : 0 < σ₁ := by calc
    1 - A / (Real.log T)^9 >= 1 - (1/2) / 1 ^ 9:= by
      gcongr
      · exact A_in_Ioc.2
      · exact (logt_gt_one T_gt_3.le).le
    _ > 0 := by norm_num
  have σ₁_lt_one : σ₁ < 1 := by
    apply sub_lt_self
    apply div_pos A_in_Ioc.1
    bound

  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at holo2

  have holo2a : HolomorphicOn (SmoothedChebyshevIntegrand ν ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}) := by
    apply DifferentiableOn.mul
    · apply DifferentiableOn.mul
      · rw [(by ext; ring : (fun s ↦ -ζ' s / ζ s) = (fun s ↦ -(ζ' s / ζ s)))]
        apply DifferentiableOn.neg holo2
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        apply Smooth1MellinDifferentiable ContDiff1ν ν_supp ⟨ε_pos, ε_lt_one⟩ ν_nonneg ν_massOne
        linarith[mem_reProdIm.mp hs.1 |>.1.1]
    · intro s hs
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_cpow (by fun_prop)
      left
      norm_cast
      linarith
  have ψ_ε_diff :
      ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖ ≤
        ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ +
        ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ +
        c₅ * X ^ σ₂ / ε + ‖I₆ ν ε X σ₁ σ₂‖ +
        ‖I₇ ν ε T X σ₁‖ + ‖I₈ ν ε T X σ₁‖ +
        ‖I₉ ν ε X T‖ :=
    hContour X ε T σ₁ X_gt_3 ε_pos ε_lt_one T_gt_3 σ₁pos σ₁_lt_one
      σ₂_lt_σ₁ holo1 holo2a
  specialize h_main ε ⟨ε_pos, ε_lt_ε_main⟩
  have main : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ ≤ C_main * ε * X := by
    nth_rewrite 2 [← one_mul X]
    push_cast
    rw [← sub_mul, norm_mul]
    gcongr
    rw [norm_real, norm_of_nonneg (by linarith)]
  specialize hc₁ ε ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₂ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₃ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₄ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₄
  have hc₇ : ‖I₇ ν ε T X σ₁‖ ≤
      c₇ * X * X ^ (-A / (Real.log T ^ 9)) / ε := by
    have hI7 : I₇ ν ε T X σ₁ = conj (I₃ ν ε T X σ₁) := by
      unfold I₃ I₇
      simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
      rw [neg_mul, mul_neg, ← neg_mul]
      congr
      · ring
      · rw [← intervalIntegral_conj, ← intervalIntegral.integral_comp_neg]
        apply intervalIntegral.integral_congr
        intro t ht
        simp only
        rw [← smoothedChebyshevIntegrand_conj (by linarith : 0 < X)]
        simp
    rw [hI7, norm_conj]
    exact hc₃
  have hc₈ : ‖I₈ ν ε T X σ₁‖ ≤ c₈ * X / (ε * T) := by
    have hI8 : I₈ ν ε T X σ₁ = -conj (I₂ ν ε T X σ₁) := by
      unfold I₂ I₈
      rw [map_mul, ← neg_mul]
      congr
      · simp [conj_ofNat]
      · rw [← intervalIntegral_conj]
        apply intervalIntegral.integral_congr
        intro σ hσ
        simp only []
        rw [← smoothedChebyshevIntegrand_conj (by linarith : 0 < X)]
        simp only [map_sub, conj_ofReal, map_mul, conj_I, mul_neg, sub_neg_eq_add]
    rw [hI8, norm_neg, norm_conj]
    exact hc₂
  have hc₉ : ‖I₉ ν ε X T‖ ≤ c₉ * X * Real.log X / (ε * T) := by
    have hI9 : I₉ ν ε X T = conj (I₁ ν ε X T) := by
      unfold I₉ I₁
      simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
      rw [neg_mul, mul_neg, ← neg_mul]
      congr
      · ring
      · rw [← integral_conj, ← integral_comp_neg_Ioi, integral_Ici_eq_integral_Ioi]
        apply setIntegral_congr_fun <| measurableSet_Ioi
        intro t ht
        simp only
        rw [← smoothedChebyshevIntegrand_conj (by linarith : 0 < X)]
        simp
    rw [hI9, norm_conj]
    exact hc₁
  have hc₆ : ‖I₆ ν ε X σ₁ σ₂‖ ≤
      c₆ * X * X ^ (-A / (Real.log T ^ 9)) / ε := by
    have hI6 : I₆ ν ε X σ₁ σ₂ = -conj (I₄ ν ε X σ₁ σ₂) := by
      unfold I₆ I₄
      simp only [map_mul, map_div₀, conj_ofReal, conj_I, map_one, conj_ofNat]
      rw [← neg_mul]
      congr
      · ring
      · rw [← intervalIntegral_conj]
        apply intervalIntegral.integral_congr
        intro σ hσ
        simp only
        rw [← smoothedChebyshevIntegrand_conj (by linarith : 0 < X)]
        simp [conj_ofNat]
    rw [hI6, norm_neg, norm_conj]
    exact hc₄

  clear ν_nonneg ν_massOne ContDiff1ν ν_supp holo2

  have C'bnd : c_close * ε * X * Real.log X + C_main * ε * X ≤ C' * ε * X * Real.log X := by
    have : C_main * ε * X * 1 ≤ C_main * ε * X * Real.log X := by
      gcongr
    linarith

  have C''bnd : c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T) + c₈ * X / (ε * T)
    + c₉ * X * Real.log X / (ε * T) ≤ C'' * X * Real.log X / (ε * T) := by
    unfold C''
    rw [(by ring : (c₁ + c₂ + c₈ + c₉) * X * Real.log X / (ε * T)
      = c₁ * X * Real.log X / (ε * T) + c₂ * X * Real.log X / (ε * T)
        + c₈ * X * Real.log X / (ε * T) + c₉ * X * Real.log X / (ε * T))]
    have : c₂ * X / (ε * T) * 1 ≤ c₂ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₂ * X / (ε * T) ≤ c₂ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]

  have C'''bnd : c₃ * X * X ^ (-A / Real.log T ^ 9) / ε
                    + c₄ * X * X ^ (-A / Real.log T ^ 9) / ε
                    + c₆ * X * X ^ (-A / Real.log T ^ 9) / ε
                    + c₇ * X * X ^ (-A / Real.log T ^ 9) / ε
                  ≤ C''' * X * X ^ (-A / Real.log T ^ 9) / ε := by
    apply le_of_eq
    ring

  calc
    _         = ‖(ψ X - ψ_ε_of_X) + (ψ_ε_of_X - X)‖ := by ring_nf; norm_cast
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - X‖ := norm_add_le _ _
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖(ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X)
                  + (𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X)‖ := by ring_nf
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖
                  + ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ := by
                    rw [add_assoc]
                    gcongr
                    apply norm_add_le
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖
                  + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖ := by ring
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖
                  + (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖
                  + c₅ * X ^ σ₂ / ε + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖ + ‖I₈ ν ε T X σ₁‖
                  + ‖I₉ ν ε X T‖) := by gcongr
    _         ≤ c_close * ε * X * Real.log X + C_main * ε * X
                  + (c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₃ * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₄ * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₅ * X ^ σ₂ / ε
                  + c₆ * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₇ * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T)) := by
      gcongr
      convert! h_close using 1
      rw [← norm_neg]
      congr
      ring
    _         =  (c_close * ε * X * Real.log X + C_main * ε * X)
                  + ((c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T))
                  + (c₃ * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₄ * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₆ * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₇ * X * X ^ (-A / Real.log T ^ 9) / ε)
                  + c₅ * X ^ σ₂ / ε
                  ) := by ring
    _         ≤ C' * ε * X * Real.log X
                  + (C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₅ * X ^ σ₂ / ε
                  ) := by
      gcongr
    _        = C' * ε * X * Real.log X
                  + C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T ^ 9) / ε
                  + c₅ * X ^ σ₂ / ε
                    := by ring
    _        ≤ C' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10))
                  + C'' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10))
                  + C''' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10))
                  + c₅ * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10))
                    := by
      gcongr
    _        = C * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 10))
                    := by ring
    _        = _ := by
      rw [Real.norm_of_nonneg]
      · rw [← mul_assoc]
      · positivity

#print axioms MediumPNT
