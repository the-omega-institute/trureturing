/- GID: D5/S3/Entropy/RenyiCombining/CachinConvexBranch
   generality: G
   mirror-B: D5/B/S3/Entropy/RenyiCombining/CachinConvexBranch
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Riccati curvature certificate for the convex Renyi combining branch. -/
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone
import D5.S3.QuantumChannels.ContractionSpectrumOrder
/-! A removable quotient in the bias variable supplies the initial curvature data. -/
open Set Filter
open scoped Topology
namespace D5.S3.Entropy.RenyiCombining.CachinConvexInitial
private noncomputable def H (n t : ℝ) : ℝ :=
  dslope (fun s : ℝ => (1 + s) ^ n - (1 - s) ^ n) 0 t
private noncomputable def K (n t : ℝ) : ℝ := (1 + t) ^ n + (1 - t) ^ n
private noncomputable def Q (n t : ℝ) : ℝ := n * K n t / H n t
private noncomputable def pneg (n : ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  (binomialSeries ℝ n).compContinuousLinearMap (-ContinuousLinearMap.id ℝ ℝ)
private theorem neg_series (n : ℝ) : HasFPowerSeriesAt (fun t : ℝ => (1 - t) ^ n) (pneg n) 0 := by
  have hp : HasFPowerSeriesAt (fun t : ℝ => (1 + t) ^ n) (binomialSeries ℝ n)
      ((-ContinuousLinearMap.id ℝ ℝ) (0 : ℝ)) := by
    simpa using (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := n))
  simpa [pneg, sub_eq_add_neg, Function.comp_def] using hp.compContinuousLinearMap
private theorem H_series (n : ℝ) : HasFPowerSeriesAt (H n) ((binomialSeries ℝ n - pneg n).fslope) 0 := by
  exact ((Real.one_add_rpow_hasFPowerSeriesAt_zero (a := n)).sub
    (neg_series n)).has_fpower_series_dslope_fslope
private theorem K_series (n : ℝ) : HasFPowerSeriesAt (K n) (binomialSeries ℝ n + pneg n) 0 := by
  exact (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := n)).add (neg_series n)
private theorem iteratedDeriv_of_series {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ} (hp : HasFPowerSeriesAt f p 0) (k : ℕ) : iteratedDeriv k f 0 = (k.factorial : ℝ) * p.coeff k := by
  have he := congrArg (fun q : FormalMultilinearSeries ℝ ℝ ℝ => q.coeff k)
    (hp.eq_formalMultilinearSeries hp.analyticAt.hasFPowerSeriesAt)
  simp only [FormalMultilinearSeries.coeff_ofScalars] at he
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hf] at he
  nlinarith [he]
private theorem H_deriv (n : ℝ) (k : ℕ) : iteratedDeriv k (H n) 0 = (k.factorial : ℝ) * (Ring.choose n (k + 1) - (-1 : ℝ) ^ (k + 1) * Ring.choose n (k + 1)) := by
  rw [iteratedDeriv_of_series (H_series n), FormalMultilinearSeries.coeff_fslope]
  simp [pneg, binomialSeries, FormalMultilinearSeries.ofScalars_comp_neg_id,
    FormalMultilinearSeries.coeff, FormalMultilinearSeries.ofScalars, List.prod_ofFn]
private theorem K_deriv (n : ℝ) (k : ℕ) : iteratedDeriv k (K n) 0 = (k.factorial : ℝ) * (Ring.choose n k + (-1 : ℝ) ^ k * Ring.choose n k) := by
  rw [iteratedDeriv_of_series (K_series n)]
  simp [pneg, binomialSeries, FormalMultilinearSeries.ofScalars_comp_neg_id,
    FormalMultilinearSeries.coeff, FormalMultilinearSeries.ofScalars, List.prod_ofFn]
private theorem H_zero (n : ℝ) : H n 0 = 2 * n := by
  have h := H_deriv n 0
  simp [Ring.choose_one_right] at h
  linarith
private theorem Q_analyticAt_zero {n : ℝ} (hn : n ≠ 0) : AnalyticAt ℝ (Q n) 0 := by
  exact ((show AnalyticAt ℝ (fun _ : ℝ => n) 0 from analyticAt_const).mul
    (K_series n).analyticAt).div (H_series n).analyticAt
    (by rw [H_zero]; exact mul_ne_zero (by norm_num) hn)
private theorem Q_zero {n : ℝ} (hn : n ≠ 0) : Q n 0 = 1 := by
  norm_num [Q, K, H_zero]
  field_simp
/-- The desingularized quotient agrees with the elementary real-power formula away from zero. -/
private theorem Q_eq {n t : ℝ} (ht : t ≠ 0) : Q n t = n * t * ((1 + t) ^ n + (1 - t) ^ n) / ((1 + t) ^ n - (1 - t) ^ n) := by
  simp only [Q, K, H, dslope_of_ne _ ht, slope_def_field, sub_zero, add_zero, Real.one_rpow, sub_self]
  rw [div_div_eq_mul_div]
  ring
private theorem H_jets (n : ℝ) : iteratedDeriv 1 (H n) 0 = 0 ∧ iteratedDeriv 2 (H n) 0 = 2 * n * (n - 1) * (n - 2) / 3 ∧ iteratedDeriv 3 (H n) 0 = 0 ∧ iteratedDeriv 4 (H n) 0 = 2 * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 5 := by
  simp only [H_deriv]
  norm_num [Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
    Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, smul_eq_mul]
  <;> ring_nf <;> norm_num
private theorem K_jets (n : ℝ) : K n 0 = 2 ∧ iteratedDeriv 1 (K n) 0 = 0 ∧ iteratedDeriv 2 (K n) 0 = 2 * n * (n - 1) ∧ iteratedDeriv 3 (K n) 0 = 0 ∧ iteratedDeriv 4 (K n) 0 = 2 * n * (n - 1) * (n - 2) * (n - 3) := by
  simp only [K_deriv]
  norm_num [K, Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
    Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, smul_eq_mul]
  <;> ring_nf <;> norm_num
private theorem Q_jets {n : ℝ} (hn : n ≠ 0) : iteratedDeriv 1 (Q n) 0 = 0 ∧
    iteratedDeriv 2 (Q n) 0 = 2 * (n ^ 2 - 1) / 3 ∧
    iteratedDeriv 3 (Q n) 0 = 0 ∧
    iteratedDeriv 4 (Q n) 0 = -8 * (1 - n ^ 2) * (4 - n ^ 2) / 15 := by
  have ha := Q_analyticAt_zero hn
  have hh := (H_series n).analyticAt
  have hk := (K_series n).analyticAt
  have hne : H n 0 ≠ 0 := by rw [H_zero]; exact mul_ne_zero (by norm_num) hn
  have he : (fun t => Q n t * H n t) =ᶠ[𝓝 0] (fun t => n * K n t) := by
    filter_upwards [hh.continuousAt.eventually_ne hne] with t ht
    simp [Q, ht]
  have hrecur (k : ℕ) :
      (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        iteratedDeriv i (Q n) 0 * iteratedDeriv (k - i) (H n) 0) =
        n * iteratedDeriv k (K n) 0 := by
    have h := he.iteratedDeriv_eq k
    rw [iteratedDeriv_fun_mul ha.contDiffAt hh.contDiffAt,
      iteratedDeriv_const_mul_field] at h
    exact h
  obtain ⟨hH1, hH2, hH3, hH4⟩ := H_jets n
  obtain ⟨hK0, hK1, hK2, hK3, hK4⟩ := K_jets n
  have h1 := hrecur 1
  have h2 := hrecur 2
  have h3 := hrecur 3
  have h4 := hrecur 4
  norm_num [Finset.sum_range_succ, H_zero, Q_zero hn, hH1, hH2, hH3, hH4,
    hK0, hK1, hK2, hK3, hK4, Nat.choose] at h1 h2 h3 h4
  have hQ1 : deriv (Q n) 0 = 0 := h1.resolve_right hn
  have hQ2 : iteratedDeriv 2 (Q n) 0 = 2 * (n ^ 2 - 1) / 3 := by
    have : n * (iteratedDeriv 2 (Q n) 0 - 2 * (n ^ 2 - 1) / 3) = 0 := by
      nlinarith [h2]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hn)
  have hQ3 : iteratedDeriv 3 (Q n) 0 = 0 := by
    rw [hQ1] at h3
    exact (mul_eq_zero.mp (by nlinarith [h3] : n * iteratedDeriv 3 (Q n) 0 = 0)).resolve_left hn
  refine ⟨by simpa using hQ1, hQ2, hQ3, ?_⟩
  rw [hQ2] at h4
  have : n * (iteratedDeriv 4 (Q n) 0 -
      (-8 * (1 - n ^ 2) * (4 - n ^ 2) / 15)) = 0 := by nlinarith [h4]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hn)
private theorem Q_local_derivatives {n : ℝ} (hn : n ≠ 0) :
    ∃ a : ℝ, 0 < a ∧
      (∀ t ∈ Icc 0 a, ∀ k : ℕ,
        HasDerivAt (iteratedDeriv k (Q n)) (iteratedDeriv (k + 1) (Q n) t) t) ∧
      ContinuousAt (iteratedDeriv 4 (Q n)) 0 := by
  have ha := Q_analyticAt_zero hn
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp ha.eventually_analyticAt
  refine ⟨ε / 2, by linarith, ?_, ?_⟩
  · intro t ht k
    have hat : AnalyticAt ℝ (Q n) t := he (by
      simp only [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      linarith [ht.2])
    have hak : AnalyticAt ℝ (iteratedDeriv k (Q n)) t := by
      simpa only [iteratedDeriv_eq_iterate] using hat.iterated_deriv k
    simpa only [iteratedDeriv_succ] using hak.differentiableAt.hasDerivAt
  · have hak : AnalyticAt ℝ (iteratedDeriv 4 (Q n)) 0 := by
      simpa only [iteratedDeriv_eq_iterate] using ha.iterated_deriv 4
    exact hak.differentiableAt.continuousAt
end D5.S3.Entropy.RenyiCombining.CachinConvexInitial
open Set Filter
open scoped Topology
namespace D5.S3.Entropy.RenyiCombining.CachinConvexLimits
private noncomputable def sqrtSlope (Q₁ : ℝ → ℝ) (z : ℝ) : ℝ :=
  Q₁ (Real.sqrt z) / (2 * Real.sqrt z)
private noncomputable def sqrtCurvature (Q₁ Q₂ : ℝ → ℝ) (z : ℝ) : ℝ :=
  (Real.sqrt z * Q₂ (Real.sqrt z) - Q₁ (Real.sqrt z)) /
    (4 * (Real.sqrt z) ^ (3 : ℕ))
private theorem sqrt_comp_hasDerivAt {Q Q₁ : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hQ : HasDerivAt Q (Q₁ (Real.sqrt z)) (Real.sqrt z)) :
    HasDerivAt (fun x => Q (Real.sqrt x)) (sqrtSlope Q₁ z) z := by
  convert hQ.comp z (Real.hasDerivAt_sqrt hz.ne') using 1 <;>
    simp only [sqrtSlope, Function.comp_def, div_eq_mul_inv, one_mul]
private theorem sqrtSlope_hasDerivAt {Q₁ Q₂ : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hQ : HasDerivAt Q₁ (Q₂ (Real.sqrt z)) (Real.sqrt z)) :
    HasDerivAt (sqrtSlope Q₁) (sqrtCurvature Q₁ Q₂ z) z := by
  have ht := Real.sqrt_pos.mpr hz
  have hs := Real.hasDerivAt_sqrt hz.ne'
  convert (hQ.comp z hs).div (hs.const_mul 2) (by positivity : 2 * Real.sqrt z ≠ 0) using 1
  · rfl
  · dsimp [sqrtCurvature]
    field_simp [ht.ne']
    <;> ring
private theorem jet_signs_on_interval {Q₁ Q₂ Q₃ Q₄ : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (k : ℝ)
    (h₁ : ∀ t ∈ Icc 0 a, HasDerivAt Q₁ (Q₂ t) t)
    (h₂ : ∀ t ∈ Icc 0 a, HasDerivAt Q₂ (Q₃ t) t)
    (h₃ : ∀ t ∈ Icc 0 a, HasDerivAt Q₃ (Q₄ t) t)
    (h₁₀ : Q₁ 0 = 0) (h₃₀ : Q₃ 0 = 0) (h₂₀ : Q₂ 0 < 2 * k)
    (h₄neg : ∀ t ∈ Ioo 0 a, Q₄ t < 0) :
    ∀ t ∈ Ioo 0 a, Q₁ t < 2 * k * t ∧ t * Q₂ t - Q₁ t < 0 := by
  have hm₃ : StrictAntiOn Q₃ (Icc 0 a) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t ht => (h₃ t ht).continuousAt.continuousWithinAt) (by
        intro t ht
        rw [interior_Icc] at ht
        rw [(h₃ t ⟨ht.1.le, ht.2.le⟩).deriv]
        exact h₄neg t ht)
  have hQ₃ : ∀ t ∈ Ioo 0 a, Q₃ t < 0 := by
    intro t ht
    have h := hm₃ ⟨le_rfl, ha.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa only [h₃₀] using h
  have hm₂ : StrictAntiOn Q₂ (Icc 0 a) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t ht => (h₂ t ht).continuousAt.continuousWithinAt) (by
        intro t ht
        rw [interior_Icc] at ht
        rw [(h₂ t ⟨ht.1.le, ht.2.le⟩).deriv]
        exact hQ₃ t ht)
  have hQ₂ : ∀ t ∈ Icc 0 a, Q₂ t < 2 * k := by
    intro t ht
    exact lt_of_le_of_lt (hm₂.antitoneOn ⟨le_rfl, ha.le⟩ ht ht.1) h₂₀
  have hshift : ∀ t ∈ Icc 0 a,
      HasDerivAt (fun x => Q₁ x - 2 * k * x) (Q₂ t - 2 * k) t := by
    intro t ht
    convert (h₁ t ht).sub ((hasDerivAt_id t).const_mul (2 * k)) using 1
    · rfl
    · ring
  have hm₁ : StrictAntiOn (fun x => Q₁ x - 2 * k * x) (Icc 0 a) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t ht => (hshift t ht).continuousAt.continuousWithinAt) (by
        intro t ht
        rw [(hshift t (interior_subset ht)).deriv]
        exact sub_neg.mpr (hQ₂ t (interior_subset ht)))
  have hN : ∀ t ∈ Icc 0 a,
      HasDerivAt (fun x => x * Q₂ x - Q₁ x) (t * Q₃ t) t := by
    intro t ht
    convert ((hasDerivAt_id t).mul (h₂ t ht)).sub (h₁ t ht) using 1
    · rfl
    · dsimp
      ring
  have hmN : StrictAntiOn (fun x => x * Q₂ x - Q₁ x) (Icc 0 a) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t ht => (hN t ht).continuousAt.continuousWithinAt) (by
        intro t ht
        have ht' : t ∈ Ioo 0 a := by simpa only [interior_Icc] using ht
        rw [(hN t (interior_subset ht)).deriv]
        exact mul_neg_of_pos_of_neg ht'.1 (hQ₃ t ht'))
  intro t ht
  constructor
  · have h := hm₁ ⟨le_rfl, ha.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
    simp only [h₁₀, mul_zero, sub_self] at h
    linarith
  · have h := hmN ⟨le_rfl, ha.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa only [zero_mul, h₁₀, sub_self] using h
private theorem exists_sqrt_jet_negative {Q₁ Q₂ Q₃ Q₄ : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (k : ℝ)
    (h₁ : ∀ t ∈ Icc 0 a, HasDerivAt Q₁ (Q₂ t) t)
    (h₂ : ∀ t ∈ Icc 0 a, HasDerivAt Q₂ (Q₃ t) t)
    (h₃ : ∀ t ∈ Icc 0 a, HasDerivAt Q₃ (Q₄ t) t)
    (h₁₀ : Q₁ 0 = 0) (h₃₀ : Q₃ 0 = 0) (h₂₀ : Q₂ 0 < 2 * k)
    (h₄cont : ContinuousAt Q₄ 0) (h₄₀ : Q₄ 0 < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Ioo 0 δ,
      sqrtSlope Q₁ z < k ∧ sqrtCurvature Q₁ Q₂ z < 0 := by
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), Q₄ t < 0 :=
    h₄cont.eventually (eventually_lt_nhds h₄₀)
  obtain ⟨b, hb, hbound⟩ := Metric.eventually_nhds_iff.mp he
  let c := min a (b / 2)
  have hc : 0 < c := lt_min ha (by linarith)
  have hc₁ : c ≤ a := min_le_left _ _
  have hc₂ : c < b := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsub : Icc (0 : ℝ) c ⊆ Icc 0 a := Icc_subset_Icc le_rfl hc₁
  have hsign := jet_signs_on_interval hc k
    (fun t ht => h₁ t (hsub ht)) (fun t ht => h₂ t (hsub ht))
    (fun t ht => h₃ t (hsub ht)) h₁₀ h₃₀ h₂₀ (by
      intro t ht
      apply hbound
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      exact ht.2.trans hc₂)
  refine ⟨c ^ (2 : ℕ), sq_pos_of_pos hc, ?_⟩
  intro z hz
  have ht : Real.sqrt z ∈ Ioo 0 c := by
    constructor
    · exact Real.sqrt_pos.mpr hz.1
    · apply (Real.sqrt_lt' hc).mpr
      exact hz.2
  obtain ⟨hfirst, hsecond⟩ := hsign _ ht
  constructor
  · apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) ht.1)).mpr
    nlinarith
  · exact div_neg_of_neg_of_pos hsecond (mul_pos (by norm_num) (pow_pos ht.1 _))
end D5.S3.Entropy.RenyiCombining.CachinConvexLimits
/-! The declarations concern differential inequalities for arbitrary real functions,
not finite calculations or certified numerical instances. -/
open Set Filter
open scoped Topology
namespace D5.S3.Entropy.RenyiCombining.CachinConvexBranch
/-- A negative curvature cannot cross zero when its derivative is negative at every
possible first crossing. The companion first derivative is kept negative by integration. -/
private theorem curvature_neg_of_first_zero (g f f' : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hg : ContinuousOn g (Icc 0 a)) (hf : ContinuousOn f (Icc 0 a))
    (hg' : ∀ z ∈ Ioo 0 a, HasDerivAt g (f z) z)
    (hf' : ∀ z ∈ Ioc 0 a, HasDerivAt f (f' z) z)
    (hg0 : g 0 < 0) (hf0 : f 0 < 0)
    (hbarrier : ∀ z ∈ Ioc 0 a, f z = 0 → g z < 0 → f' z < 0) :
    ∀ z ∈ Icc 0 a, f z < 0 := by
  intro z hz
  by_contra hn
  have hzn : 0 ≤ f z := le_of_not_gt hn
  let S : Set ℝ := {x ∈ Icc 0 a | 0 ≤ f x}
  have hSclosed : IsClosed S := isClosed_Icc.isClosed_le continuousOn_const hf
  have hScompact : IsCompact S := isCompact_Icc.of_isClosed_subset hSclosed (by
    intro x hx; exact hx.1)
  obtain ⟨b, hbS, hbmin⟩ := hScompact.exists_isLeast ⟨z, hz, hzn⟩
  have hb0 : 0 < b := by
    have hb : 0 ≤ b := hbS.1.1
    by_contra h
    have : b = 0 := le_antisymm (le_of_not_gt h) hb
    subst b
    exact (not_le_of_gt hf0) hbS.2
  have hba : b ≤ a := hbS.1.2
  have hbefore : ∀ x ∈ Ico 0 b, f x < 0 := by
    intro x hx
    by_contra hxneg
    have hxS : x ∈ S := ⟨⟨hx.1, hx.2.le.trans hba⟩, le_of_not_gt hxneg⟩
    exact (not_le_of_gt hx.2) (hbmin hxS)
  have hfb : f b = 0 := by
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hb0.le
      (hf.mono (Icc_subset_Icc le_rfl hba)) ⟨hf0.le, hbS.2⟩
    have hcS : c ∈ S := ⟨⟨hc.1, hc.2.trans hba⟩, by rw [hfc]⟩
    have : c = b := le_antisymm hc.2 (hbmin hcS)
    simpa [this] using hfc
  have hfm : ∀ x ∈ Icc 0 b, f x ≤ 0 := by
    intro x hx
    rcases lt_or_eq_of_le hx.2 with hlt | rfl
    · exact (hbefore x ⟨hx.1, hlt⟩).le
    · exact hfb.le
  have hgm : AntitoneOn g (Icc 0 b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (hg.mono (Icc_subset_Icc le_rfl hba))
      (fun x hx => (hg' x (by
        have hxi : x ∈ Ioo 0 b := by simpa using hx
        exact ⟨hxi.1, hxi.2.trans_le hba⟩)).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        have hxi : x ∈ Ioo 0 b := by simpa using hx
        rw [(hg' x ⟨hxi.1, hxi.2.trans_le hba⟩).deriv]
        exact hfm x ⟨hxi.1.le, hxi.2.le⟩)
  have hgb : g b < 0 := (hgm ⟨le_rfl, hb0.le⟩ ⟨hb0.le, le_rfl⟩ hb0.le).trans_lt hg0
  have hfb' : f' b < 0 := hbarrier b ⟨hb0, hba⟩ hfb hgb
  have hnonneg : 0 ≤ f' b := by
    apply ge_of_tendsto ((hasDerivAt_iff_tendsto_slope_left_right.mp
      (hf' b ⟨hb0, hba⟩)).1)
    have hlow : ∀ᶠ x in 𝓝[<] b, 0 < x :=
      (eventually_gt_nhds hb0).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlow, self_mem_nhdsWithin] with x hx0 hxb
    rw [slope_def_field, hfb, sub_zero]
    exact div_nonneg_iff.mpr (Or.inr ⟨(hbefore x ⟨hx0.le, hxb⟩).le,
      sub_nonpos.mpr hxb.le⟩)
  exact (not_le_of_gt hfb') hnonneg
/-- Logarithmic inverse hyperbolic tangent, in natural-log units. -/
private noncomputable def artanh (t : ℝ) : ℝ := (Real.log (1 + t) - Real.log (1 - t)) / 2
private theorem artanh_eq_real {t : ℝ} (ht : t ∈ Ioo (-1) 1) : artanh t = Real.artanh t := by
  rw [Real.artanh_eq_half_log ⟨ht.1.le, ht.2.le⟩,
    Real.log_div (by linarith [ht.1]) (by linarith [ht.2])]
  unfold artanh
  ring
/-- The auxiliary quotient, with both removable singularities filled explicitly. -/
private noncomputable def C (n z : ℝ) : ℝ :=
  if z = 0 then 1 else
    if n = 0 then Real.sqrt z / artanh (Real.sqrt z)
    else n * Real.sqrt z * Real.cosh (n * artanh (Real.sqrt z)) /
      Real.sinh (n * artanh (Real.sqrt z))
private noncomputable def D (n z : ℝ) : ℝ := C n z + n * z
/-- Elasticity in the squared-bias coordinate. -/
private noncomputable def elasticity (D D₁ : ℝ → ℝ) (z : ℝ) : ℝ := 1 - 2 * z * D₁ z / D z
/-- The rational witness gives a strict negative initial slope uniformly over the
entire parameter interval needed by the conjecture. -/
private theorem initial_slope_bound (n : ℝ) (hn : -1 < n) (hn' : n ≤ 1 / 4) :
    (n ^ 2 + 3 * n - 1) / 3 ≤ -(1 / 16 : ℝ) := by
  have hprod : 0 ≤ (1 / 4 - n) * (n + 13 / 4) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith
/-- The logarithmic derivative of the denominator gives a strictly increasing
elasticity whenever its first two derivatives are negative. -/
private theorem elasticity_hasDerivAt (D D₁ D₂ : ℝ → ℝ) (z : ℝ) (hD : D z ≠ 0)
    (hd : HasDerivAt D (D₁ z) z) (hd₁ : HasDerivAt D₁ (D₂ z) z) :
    HasDerivAt (elasticity D D₁)
      (-2 * D₁ z / D z - 2 * z * D₂ z / D z +
        2 * z * (D₁ z) ^ 2 / (D z) ^ 2) z := by
  convert (hasDerivAt_const z 1).sub
    ((((hasDerivAt_id z).const_mul 2).mul hd₁).div hd hD) using 1
  · rfl
  · dsimp
    field_simp
    <;> ring
private theorem elasticity_strictMonoOn (D D₁ D₂ : ℝ → ℝ) (a b : ℝ)
    (hpos : ∀ z ∈ Ioo a b, 0 < z ∧ 0 < D z)
    (hd : ∀ z ∈ Ioo a b, HasDerivAt D (D₁ z) z)
    (hd₁ : ∀ z ∈ Ioo a b, HasDerivAt D₁ (D₂ z) z)
    (hneg₁ : ∀ z ∈ Ioo a b, D₁ z < 0)
    (hneg₂ : ∀ z ∈ Ioo a b, D₂ z < 0) :
    StrictMonoOn (elasticity D D₁) (Ioo a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    (fun z hz => (elasticity_hasDerivAt D D₁ D₂ z (hpos z hz).2.ne'
      (hd z hz) (hd₁ z hz)).continuousAt.continuousWithinAt)
  intro z hz
  have hz' : z ∈ Ioo a b := by simpa using hz
  have hp := hpos z hz'
  rw [(elasticity_hasDerivAt D D₁ D₂ z hp.2.ne' (hd z hz') (hd₁ z hz')).deriv]
  have h₁ : 0 < -2 * D₁ z / D z :=
    div_pos (mul_pos_of_neg_of_neg (by norm_num) (hneg₁ z hz')) hp.2
  have h₂ : 0 < -(2 * z * D₂ z) / D z :=
    div_pos (neg_pos.mpr (mul_neg_of_pos_of_neg (mul_pos (by norm_num) hp.1) (hneg₂ z hz'))) hp.2
  have h₃ : 0 ≤ 2 * z * (D₁ z) ^ 2 / (D z) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp.1.le) (sq_nonneg _)) (sq_nonneg _)
  have h₂' : 0 < -2 * z * D₂ z / D z := by convert h₂ using 1 <;> ring
  have hres := add_pos_of_pos_of_nonneg (add_pos h₁ h₂') h₃
  convert hres using 1 <;> ring
private theorem artanh_pos (t : ℝ) (ht : t ∈ Ioo 0 1) : 0 < artanh t := by
  rw [artanh_eq_real ⟨by linarith [ht.1], ht.2⟩]
  exact Real.artanh_pos ht
private theorem artanh_hasDerivAt (t : ℝ) (ht : t ∈ Ioo 0 1) :
    HasDerivAt artanh (1 / (1 - t ^ 2)) t := by
  have he : artanh =ᶠ[𝓝 t] Real.artanh := by
    filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo (-1 : ℝ) 1 from
      ⟨by linarith [ht.1], ht.2⟩)] with s hs
    exact artanh_eq_real hs
  exact (D5.S3.QuantumChannels.ContractionSpectrumOrder.hasDerivAt_artanh
    ⟨by linarith [ht.1], ht.2⟩).congr_of_eventuallyEq he
private theorem C_pos (n z : ℝ) (hn : 0 < n) (hz : z ∈ Ioo 0 1) : 0 < C n z := by
  have ht : Real.sqrt z ∈ Ioo 0 1 := ⟨Real.sqrt_pos.mpr hz.1,
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hz.2)⟩
  have hu := artanh_pos _ ht
  simp only [C, if_neg hz.1.ne', if_neg hn.ne']
  exact div_pos (mul_pos (mul_pos hn ht.1) (Real.cosh_pos _))
    (Real.sinh_pos_iff.mpr (mul_pos hn hu))
private theorem D_pos (n z : ℝ) (hn : 0 < n) (hz : z ∈ Ioo 0 1) : 0 < D n z := by
  exact add_pos (C_pos n z hn hz) (mul_pos hn hz.1)
/-- The explicit hyperbolic quotient satisfies the Riccati equation in the open interval. -/
private theorem C_hasDerivAt (n z : ℝ) (hn : 0 < n) (hz : z ∈ Ioo 0 1) :
    HasDerivAt (C n)
      (((1 - z) * C n z - (C n z) ^ 2 + n ^ 2 * z) / (2 * z * (1 - z))) z := by
  let t := Real.sqrt z
  have ht : t ∈ Ioo 0 1 := ⟨Real.sqrt_pos.mpr hz.1,
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hz.2)⟩
  have htz : t ^ 2 = z := Real.sq_sqrt hz.1.le
  have htne : t ≠ 0 := ht.1.ne'
  have h1t : 1 - t ^ 2 ≠ 0 := by rw [htz]; linarith [hz.2]
  have hs : Real.sinh (n * artanh t) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hn (artanh_pos t ht))).ne'
  have hd := Real.hasDerivAt_sqrt hz.1.ne'
  have hu := (artanh_hasDerivAt t ht).comp z hd
  have hnu := hu.const_mul n
  have hraw := (((hd.const_mul n).mul hnu.cosh).div hnu.sinh hs)
  have heq : C n =ᶠ[𝓝 z] (fun x => n * Real.sqrt x *
      Real.cosh (n * artanh (Real.sqrt x)) / Real.sinh (n * artanh (Real.sqrt x))) := by
    filter_upwards [eventually_ne_nhds hz.1.ne'] with x hx
    simp only [C, if_neg hx, if_neg hn.ne']
  apply (hraw.congr_of_eventuallyEq heq).congr_deriv
  simp only [C, if_neg hz.1.ne', if_neg hn.ne']
  change ((n * (1 / (2 * t)) * Real.cosh (n * artanh t) + n * t *
      (Real.sinh (n * artanh t) * (n * (1 / (1 - t ^ 2) * (1 / (2 * t)))))) *
      Real.sinh (n * artanh t) - n * t * Real.cosh (n * artanh t) *
      (Real.cosh (n * artanh t) * (n * (1 / (1 - t ^ 2) * (1 / (2 * t)))))) /
      Real.sinh (n * artanh t) ^ 2 = _
  have hh : Real.cosh (n * artanh t) ^ 2 = 1 + Real.sinh (n * artanh t) ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (n * artanh t)]
  change _ = ((1 - z) * (n * t * Real.cosh (n * artanh t) / Real.sinh (n * artanh t)) -
      (n * t * Real.cosh (n * artanh t) / Real.sinh (n * artanh t)) ^ 2 + n ^ 2 * z) /
      (2 * z * (1 - z))
  rw [← htz]
  field_simp [htne, hs, h1t]
  nlinarith [hh]
/-- Translation of the first-crossing argument to any nonsingular initial point. -/
private theorem curvature_neg_of_first_zero_from (g f f' : ℝ → ℝ) (l a : ℝ) (hla : l < a)
    (hg : ContinuousOn g (Icc l a)) (hf : ContinuousOn f (Icc l a))
    (hg' : ∀ z ∈ Ioo l a, HasDerivAt g (f z) z)
    (hf' : ∀ z ∈ Ioc l a, HasDerivAt f (f' z) z)
    (hgl : g l < 0) (hfl : f l < 0)
    (hbarrier : ∀ z ∈ Ioc l a, f z = 0 → g z < 0 → f' z < 0) :
    ∀ z ∈ Icc l a, f z < 0 := by
  have hmap : MapsTo (fun x => l + x) (Icc 0 (a - l)) (Icc l a) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have htranslate := curvature_neg_of_first_zero
    (fun x => g (l + x)) (fun x => f (l + x)) (fun x => f' (l + x)) (a - l)
    (sub_pos.mpr hla)
    (hg.comp (continuous_const.add continuous_id).continuousOn hmap)
    (hf.comp (continuous_const.add continuous_id).continuousOn hmap)
    (fun x hx => by
      have hd := (hg' (l + x) (by constructor <;> linarith [hx.1, hx.2])).comp x
        ((hasDerivAt_const x l).add (hasDerivAt_id x))
      convert hd using 1 <;> (try ext w) <;> (try dsimp) <;> ring)
    (fun x hx => by
      have hd := (hf' (l + x) (by constructor <;> linarith [hx.1, hx.2])).comp x
        ((hasDerivAt_const x l).add (hasDerivAt_id x))
      convert hd using 1 <;> (try ext w) <;> (try dsimp) <;> ring)
    (by simpa using hgl) (by simpa using hfl)
    (fun x hx => hbarrier (l + x) (by constructor <;> linarith [hx.1, hx.2]))
  intro z hz
  have := htranslate (z - l) (by constructor <;> linarith [hz.1, hz.2])
  simpa using this
/-- Only a punctured right-neighborhood of the singular endpoint needs initial
curvature information; no differentiability at zero is assumed. -/
private theorem riccati_curvature_neg_of_local (C C₁ C₂ C₃ : ℝ → ℝ)
    (hc₁ : ContinuousOn C₁ (Ioo 0 1)) (hc₂ : ContinuousOn C₂ (Ioo 0 1))
    (hd₁ : ∀ z ∈ Ioo 0 1, HasDerivAt C₁ (C₂ z) z)
    (hd₂ : ∀ z ∈ Ioo 0 1, HasDerivAt C₂ (C₃ z) z)
    (hlocal : ∃ ε > 0, ∀ z ∈ Ioo 0 ε, C₁ z < 0 ∧ C₂ z < 0)
    (hode : ∀ z ∈ Ioo 0 1,
      2 * z * (1 - z) * C₃ z = (-3 + 7 * z - 2 * C z) * C₂ z +
        2 * C₁ z * (1 - C₁ z)) :
    ∀ z ∈ Ioo 0 1, C₂ z < 0 := by
  obtain ⟨ε, hε, hlocal⟩ := hlocal
  intro z hz
  let l := min (z / 2) (ε / 2)
  have hl : 0 < l := lt_min (by linarith [hz.1]) (by linarith)
  have hlz : l < z := (min_le_left _ _).trans_lt (by linarith [hz.1])
  have hlε : l < ε := (min_le_right _ _).trans_lt (by linarith)
  have hsub : Icc l z ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hl.trans_le hx.1, hx.2.trans_lt hz.2⟩
  have hneg := curvature_neg_of_first_zero_from C₁ C₂ C₃ l z hlz
    (hc₁.mono hsub) (hc₂.mono hsub)
    (fun x hx => hd₁ x (hsub ⟨hx.1.le, hx.2.le⟩))
    (fun x hx => hd₂ x (hsub ⟨hx.1.le, hx.2⟩))
    (hlocal l ⟨hl, hlε⟩).1 (hlocal l ⟨hl, hlε⟩).2
    (by
      intro x hx hzero hfirst
      have hx' := hsub ⟨hx.1.le, hx.2⟩
      have hcoef : 0 < 2 * x * (1 - x) :=
        mul_pos (mul_pos (by norm_num) hx'.1) (by linarith [hx'.2])
      have hright : 2 * C₁ x * (1 - C₁ x) < 0 :=
        mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hfirst) (by linarith)
      have heq := hode x hx'
      rw [hzero, mul_zero, zero_add] at heq
      have hh : 2 * x * (1 - x) * C₃ x < 0 := heq.trans_lt hright
      by_contra h
      exact (not_lt_of_ge (mul_nonneg hcoef.le (le_of_not_gt h))) hh)
  exact hneg z ⟨hlz.le, le_rfl⟩
/-- Differentiating the Riccati equation once, with all hypotheses confined to the
open interval where its coefficients are nonsingular. -/
private theorem riccati_differentiate (C C₁ C₂ : ℝ → ℝ) (n z : ℝ) (hz : z ∈ Ioo 0 1)
    (hd : HasDerivAt C (C₁ z) z) (hd₁ : HasDerivAt C₁ (C₂ z) z)
    (hR : ∀ w ∈ Ioo 0 1,
      2 * w * (1 - w) * C₁ w = (1 - w) * C w - (C w) ^ 2 + n ^ 2 * w) :
    2 * z * (1 - z) * C₂ z = (-1 + 3 * z - 2 * C z) * C₁ z - C z + n ^ 2 := by
  have hL : HasDerivAt (fun w => 2 * w * (1 - w) * C₁ w)
      ((2 - 4 * z) * C₁ z + 2 * z * (1 - z) * C₂ z) z := by
    convert ((((hasDerivAt_id z).const_mul 2).mul
      ((hasDerivAt_const z 1).sub (hasDerivAt_id z))).mul hd₁) using 1 <;> (try ext w) <;> (try dsimp) <;> ring
  have hRight : HasDerivAt (fun w => (1 - w) * C w - (C w) ^ 2 + n ^ 2 * w)
      (-C z + (1 - z) * C₁ z - 2 * C z * C₁ z + n ^ 2) z := by
    convert ((((hasDerivAt_const z 1).sub (hasDerivAt_id z)).mul hd).sub
      (hd.pow 2)).add ((hasDerivAt_id z).const_mul (n ^ 2)) using 1 <;> (try ext w) <;> (try dsimp) <;> ring
  have heq : (fun w => 2 * w * (1 - w) * C₁ w) =ᶠ[𝓝 z]
      (fun w => (1 - w) * C w - (C w) ^ 2 + n ^ 2 * w) := by
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with w hw
    exact hR w hw
  have he := hL.unique (hRight.congr_of_eventuallyEq heq)
  linear_combination he
/-- A second differentiation yields the sign-preserving curvature equation used
by the first-zero argument. -/
private theorem riccati_differentiate_twice (C C₁ C₂ C₃ : ℝ → ℝ) (n z : ℝ)
    (hz : z ∈ Ioo 0 1) (hd : HasDerivAt C (C₁ z) z)
    (hd₁ : HasDerivAt C₁ (C₂ z) z) (hd₂ : HasDerivAt C₂ (C₃ z) z)
    (hR : ∀ w ∈ Ioo 0 1,
      2 * w * (1 - w) * C₂ w = (-1 + 3 * w - 2 * C w) * C₁ w - C w + n ^ 2) :
    2 * z * (1 - z) * C₃ z = (-3 + 7 * z - 2 * C z) * C₂ z +
      2 * C₁ z * (1 - C₁ z) := by
  have hL : HasDerivAt (fun w => 2 * w * (1 - w) * C₂ w)
      ((2 - 4 * z) * C₂ z + 2 * z * (1 - z) * C₃ z) z := by
    convert ((((hasDerivAt_id z).const_mul 2).mul
      ((hasDerivAt_const z 1).sub (hasDerivAt_id z))).mul hd₂) using 1 <;> (try ext w) <;> (try dsimp) <;> ring
  have hRight : HasDerivAt
      (fun w => (-1 + 3 * w - 2 * C w) * C₁ w - C w + n ^ 2)
      ((3 - 2 * C₁ z) * C₁ z + (-1 + 3 * z - 2 * C z) * C₂ z - C₁ z) z := by
    convert (((((hasDerivAt_const z (-1)).add ((hasDerivAt_id z).const_mul 3)).sub
      (hd.const_mul 2)).mul hd₁).sub hd).add (hasDerivAt_const z (n ^ 2)) using 1 <;>
      (try ext w) <;> (try dsimp) <;> ring
  have heq : (fun w => 2 * w * (1 - w) * C₂ w) =ᶠ[𝓝 z]
      (fun w => (-1 + 3 * w - 2 * C w) * C₁ w - C w + n ^ 2) := by
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with w hw
    exact hR w hw
  have he := hL.unique (hRight.congr_of_eventuallyEq heq)
  linear_combination he
/-- Conversion between the hyperbolic and real-power forms of the same quotient. -/
private theorem cosh_div_sinh_eq_rpow (n t : ℝ) (hn : 0 < n) (ht : t ∈ Ioo 0 1) :
    Real.cosh (n * artanh t) / Real.sinh (n * artanh t) =
      ((1 + t) ^ n + (1 - t) ^ n) / ((1 + t) ^ n - (1 - t) ^ n) := by
  have hp : 0 < 1 + t := by linarith [ht.1]
  have hm : 0 < 1 - t := by linarith [ht.2]
  have he : Real.exp (n * artanh t) * Real.exp (n * artanh t) =
      (1 + t) ^ n / (1 - t) ^ n := by
    rw [← Real.exp_add, Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hm, ← Real.exp_sub]
    congr 1
    unfold artanh
    ring
  have hminus : Real.exp (-(n * artanh t)) = (Real.exp (n * artanh t))⁻¹ :=
    Real.exp_neg _
  have hE : Real.exp (n * artanh t) ≠ 0 := (Real.exp_pos _).ne'
  have hQ : (1 - t) ^ n ≠ 0 := (Real.rpow_pos_of_pos hm n).ne'
  rw [Real.cosh_eq, Real.sinh_eq, hminus]
  apply (div_eq_div_iff (by
    rw [← hminus, ← Real.sinh_eq]
    exact (Real.sinh_pos_iff.mpr (mul_pos hn (artanh_pos t ht))).ne')
    (by
      have : (1 - t) ^ n < (1 + t) ^ n :=
        Real.rpow_lt_rpow hm.le (by linarith [ht.1]) hn
      linarith)).mpr
  have he' : Real.exp (n * artanh t) ^ 2 * (1 - t) ^ n = (1 + t) ^ n := by
    calc
      _ = (Real.exp (n * artanh t) * Real.exp (n * artanh t)) * (1 - t) ^ n := by ring
      _ = _ := by rw [he]; field_simp
  field_simp [hE]
  nlinarith [he']
private theorem C_eq_power_quotient (n t : ℝ) (hn : 0 < n) (ht : t ∈ Ioo 0 1) :
    C n (t ^ 2) = n * t * ((1 + t) ^ n + (1 - t) ^ n) /
      ((1 + t) ^ n - (1 - t) ^ n) := by
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero _ ht.1.ne'
  simp only [C, if_neg ht2, if_neg hn.ne', Real.sqrt_sq ht.1.le]
  calc
    _ = n * t * (Real.cosh (n * artanh t) / Real.sinh (n * artanh t)) := by ring
    _ = _ := by rw [cosh_div_sinh_eq_rpow n t hn ht]; ring
private theorem artanh_contDiffAt {m : WithTop ℕ∞} (t : ℝ) (ht : t ∈ Ioo 0 1) :
    ContDiffAt ℝ m artanh t := by
  unfold artanh
  exact (((contDiffAt_const.add contDiffAt_id).log (by dsimp; linarith [ht.1])).sub
    ((contDiffAt_const.sub contDiffAt_id).log (by dsimp; linarith [ht.2]))).div_const 2
private theorem C_contDiffAt {m : WithTop ℕ∞} (n z : ℝ) (hn : 0 < n) (hz : z ∈ Ioo 0 1) :
    ContDiffAt ℝ m (C n) z := by
  have ht : Real.sqrt z ∈ Ioo 0 1 := ⟨Real.sqrt_pos.mpr hz.1,
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hz.2)⟩
  have hs : Real.sinh (n * artanh (Real.sqrt z)) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hn (artanh_pos _ ht))).ne'
  have hsqrt : ContDiffAt ℝ m (fun x : ℝ => Real.sqrt x) z := Real.contDiffAt_sqrt hz.1.ne'
  have hnconst : ContDiffAt ℝ m (fun _ : ℝ => n) z := contDiffAt_const
  have harg := hnconst.mul ((artanh_contDiffAt (m := m) _ ht).comp z hsqrt)
  have hraw := ((hnconst.mul hsqrt).mul harg.cosh).div harg.sinh hs
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hz.1.ne'] with x hx
  simp only [C, if_neg hx, if_neg hn.ne']
  rfl
/-- The actual hyperbolic quotient satisfies the curvature equation, rather than
merely assuming that equation as a certificate input. -/
private theorem C_curvature_equation (n : ℝ) (hn : 0 < n) (z : ℝ) (hz : z ∈ Ioo 0 1) :
    2 * z * (1 - z) * deriv (deriv (deriv (C n))) z =
      (-3 + 7 * z - 2 * C n z) * deriv (deriv (C n)) z +
        2 * deriv (C n) z * (1 - deriv (C n) z) := by
  have hC : ContDiffOn ℝ 3 (C n) (Ioo 0 1) := fun x hx =>
    (C_contDiffAt (m := 3) n x hn hx).contDiffWithinAt
  have hC₁ : ContDiffOn ℝ 2 (deriv (C n)) (Ioo 0 1) :=
    hC.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hC₂ : ContDiffOn ℝ 1 (deriv (deriv (C n))) (Ioo 0 1) :=
    hC₁.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd : ∀ w ∈ Ioo 0 1, HasDerivAt (C n) (deriv (C n) w) w := by
    intro w hw
    exact ((C_hasDerivAt n w hn hw).differentiableAt).hasDerivAt
  have hd₁ : ∀ w ∈ Ioo 0 1,
      HasDerivAt (deriv (C n)) (deriv (deriv (C n)) w) w := by
    intro w hw
    exact ((hC₁.differentiableOn (by simp)) w hw).differentiableAt
      (Ioo_mem_nhds hw.1 hw.2) |>.hasDerivAt
  have hd₂ : ∀ w ∈ Ioo 0 1,
      HasDerivAt (deriv (deriv (C n))) (deriv (deriv (deriv (C n))) w) w := by
    intro w hw
    exact ((hC₂.differentiableOn (by simp)) w hw).differentiableAt
      (Ioo_mem_nhds hw.1 hw.2) |>.hasDerivAt
  have hR : ∀ w ∈ Ioo 0 1,
      2 * w * (1 - w) * deriv (C n) w =
        (1 - w) * C n w - (C n w) ^ 2 + n ^ 2 * w := by
    intro w hw
    have hden : 2 * w * (1 - w) ≠ 0 := ne_of_gt
      (mul_pos (mul_pos (by norm_num) hw.1) (by linarith [hw.2]))
    rw [(C_hasDerivAt n w hn hw).deriv]
    field_simp [hw.1.ne', sub_ne_zero.mpr hw.2.ne']
  apply riccati_differentiate_twice (C n) (deriv (C n)) (deriv (deriv (C n)))
    (deriv (deriv (deriv (C n)))) n z hz (hd z hz) (hd₁ z hz) (hd₂ z hz)
  intro w hw
  exact riccati_differentiate (C n) (deriv (C n)) (deriv (deriv (C n))) n w hw
    (hd w hw) (hd₁ w hw) hR
end D5.S3.Entropy.RenyiCombining.CachinConvexBranch
open Set Filter
open scoped Topology
namespace D5.S3.Entropy.RenyiCombining.CachinConvexLocal
open CachinConvexInitial CachinConvexLimits
private theorem C_eq_Q_sqrt (n z : ℝ) (hn : 0 < n) (hz : z ∈ Ioo 0 1) :
    CachinConvexBranch.C n z = Q n (Real.sqrt z) := by
  have ht : Real.sqrt z ∈ Ioo 0 1 :=
    ⟨Real.sqrt_pos.mpr hz.1, (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hz.2)⟩
  have h := CachinConvexBranch.C_eq_power_quotient n (Real.sqrt z) hn ht
  rw [Real.sq_sqrt hz.1.le] at h
  exact h.trans (Q_eq ht.1.ne').symm
private theorem C_local_signs (n : ℝ) (hn : 0 < n) (hn' : n ≤ 1 / 4) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Ioo 0 δ,
      deriv (CachinConvexBranch.C n) z < -n ∧
      deriv (deriv (CachinConvexBranch.C n)) z < 0 := by
  obtain ⟨a, ha, hd, hcont⟩ := Q_local_derivatives hn.ne'
  obtain ⟨h1, h2, h3, h4⟩ := Q_jets hn.ne'
  have hbound : iteratedDeriv 2 (Q n) 0 < 2 * (-n) := by
    rw [h2]
    have h := CachinConvexBranch.initial_slope_bound n (by linarith) hn'
    linarith
  have hfour : iteratedDeriv 4 (Q n) 0 < 0 := by
    rw [h4]
    have hs : n ^ (2 : ℕ) < 1 := by nlinarith
    have hp : 0 < (1 - n ^ (2 : ℕ)) * (4 - n ^ (2 : ℕ)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  obtain ⟨b, hb, hsign⟩ := exists_sqrt_jet_negative ha (-n)
    (fun t ht => by simpa using hd t ht 1)
    (fun t ht => by simpa using hd t ht 2)
    (fun t ht => by simpa using hd t ht 3) h1 h3 hbound hcont hfour
  let c := min (a ^ (2 : ℕ)) 1
  have hc : 0 < c := lt_min (sq_pos_of_pos ha) (by norm_num)
  have hroot : ∀ z ∈ Ioo 0 c, Real.sqrt z ∈ Icc 0 a := by
    intro z hz
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    exact ((Real.sqrt_lt' ha).mpr (hz.2.trans_le (min_le_left _ _))).le
  have hCE : EqOn (CachinConvexBranch.C n) (fun z => Q n (Real.sqrt z)) (Ioo 0 c) := by
    intro z hz
    exact C_eq_Q_sqrt n z hn ⟨hz.1, hz.2.trans_le (min_le_right _ _)⟩
  have hfirst : EqOn (deriv (CachinConvexBranch.C n))
      (sqrtSlope (iteratedDeriv 1 (Q n))) (Ioo 0 c) := by
    intro z hz
    have he : CachinConvexBranch.C n =ᶠ[𝓝 z] (fun w => Q n (Real.sqrt w)) :=
      hCE.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hz)
    have hQ : HasDerivAt (Q n) (iteratedDeriv 1 (Q n) (Real.sqrt z)) (Real.sqrt z) := by
      simpa using hd (Real.sqrt z) (hroot z hz) 0
    exact ((sqrt_comp_hasDerivAt hz.1 hQ).congr_of_eventuallyEq he).deriv
  have hsecond : ∀ z ∈ Ioo 0 c,
      deriv (deriv (CachinConvexBranch.C n)) z =
        sqrtCurvature (iteratedDeriv 1 (Q n)) (iteratedDeriv 2 (Q n)) z := by
    intro z hz
    have he : deriv (CachinConvexBranch.C n) =ᶠ[𝓝 z]
        sqrtSlope (iteratedDeriv 1 (Q n)) :=
      hfirst.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hz)
    have hQ := hd (Real.sqrt z) (hroot z hz) 1
    exact ((sqrtSlope_hasDerivAt hz.1 hQ).congr_of_eventuallyEq he).deriv
  refine ⟨min b c, lt_min hb hc, ?_⟩
  intro z hz
  have hzb : z ∈ Ioo 0 b := ⟨hz.1, hz.2.trans_le (min_le_left _ _)⟩
  have hzc : z ∈ Ioo 0 c := ⟨hz.1, hz.2.trans_le (min_le_right _ _)⟩
  rw [hfirst hzc, hsecond z hzc]
  exact hsign z hzb
end D5.S3.Entropy.RenyiCombining.CachinConvexLocal
/-! These identities concern arbitrary real parameters and variable coordinates. -/
open Set Filter
open scoped Topology
namespace D5.S3.Entropy.RenyiCombining.CachinConvexTransport
open CachinConvexBranch
private noncomputable def D₁ (n z : ℝ) : ℝ := deriv (C n) z + n
private theorem bias_mem (r : ℝ) (hr : r ∈ Ioo 0 1) :
    (1 - r) / (1 + r) ∈ Ioo (0 : ℝ) 1 := by
  have hp : 0 < 1 + r := by linarith [hr.1]
  constructor
  · exact div_pos (by linarith [hr.2]) hp
  · exact (div_lt_one hp).mpr (by linarith [hr.1])
private theorem C_mobius_eq (n r : ℝ) (hn : 0 < n) (hr : r ∈ Ioo 0 1) :
    C n (((1 - r) / (1 + r)) ^ 2) =
      n * ((1 - r) / (1 + r)) * (1 + r ^ n) / (1 - r ^ n) := by
  let t := (1 - r) / (1 + r)
  have ht : t ∈ Ioo (0 : ℝ) 1 := bias_mem r hr
  have hp : 0 < 1 + t := by linarith [ht.1]
  have hm : 0 < 1 - t := by linarith [ht.2]
  have hpow : (1 - t) ^ n / (1 + t) ^ n = r ^ n := by
    rw [← Real.div_rpow hm.le hp.le]
    congr 1
    apply (div_eq_iff hp.ne').mpr
    dsimp [t]
    field_simp [show 1 + r ≠ 0 by linarith [hr.1]]
    <;> ring
  have hM : (1 - t) ^ n = r ^ n * (1 + t) ^ n :=
    (div_eq_iff (Real.rpow_pos_of_pos hp n).ne').mp hpow
  have hq : r ^ n < 1 := Real.rpow_lt_one hr.1.le hr.2 hn
  change C n (t ^ 2) = _
  rw [C_eq_power_quotient n t hn ht, hM]
  change n * t * ((1 + t) ^ n + r ^ n * (1 + t) ^ n) /
      ((1 + t) ^ n - r ^ n * (1 + t) ^ n) = n * t * (1 + r ^ n) / (1 - r ^ n)
  field_simp [(Real.rpow_pos_of_pos hp n).ne', sub_ne_zero.mpr hq.ne']
  <;> ring
private theorem F_eq_denominator_elasticity (n r : ℝ) (hn : 0 < n)
    (hr : r ∈ Ioo 0 1) :
    CachinElasticityMonotone.F n r =
      elasticity (D n) (D₁ n) (((1 - r) / (1 + r)) ^ 2) := by
  let t := (1 - r) / (1 + r)
  have ht : t ∈ Ioo (0 : ℝ) 1 := bias_mem r hr
  have hz : t ^ 2 ∈ Ioo (0 : ℝ) 1 := ⟨sq_pos_of_pos ht.1, by nlinarith [ht.1, ht.2]⟩
  have hr1 : 1 + r ≠ 0 := by linarith [hr.1]
  have hqpos : 0 < r ^ n := Real.rpow_pos_of_pos hr.1 n
  have hqlt : r ^ n < 1 := Real.rpow_lt_one hr.1.le hr.2 hn
  have hq1 : 1 - r ^ n ≠ 0 := sub_ne_zero.mpr hqlt.ne'
  have hq2 : 1 + r ^ n ≠ 0 := by linarith
  have h1r : 1 - r ≠ 0 := by linarith [hr.2]
  have h1z : 1 - t ^ 2 ≠ 0 := by linarith [hz.2]
  have hc := C_mobius_eq n r hn hr
  change C n (t ^ 2) = n * t * (1 + r ^ n) / (1 - r ^ n) at hc
  have hcne : C n (t ^ 2) ≠ 0 := (C_pos n _ hn hz).ne'
  have hDne : D n (t ^ 2) ≠ 0 := (D_pos n _ hn hz).ne'
  have hA : CachinElasticityMonotone.A n r =
      ((C n (t ^ 2)) ^ 2 - n ^ 2 * t ^ 2) / ((1 - t ^ 2) * C n (t ^ 2)) := by
    rw [CachinElasticityMonotone.A_eq n r hr.1, Real.rpow_sub hr.1, Real.rpow_one, hc]
    dsimp [t]
    field_simp [hr.1.ne', hr1, hq1, hq2, h1r, hn.ne', h1z]
    <;> ring_nf
    <;> (try field_simp [hr.1.ne', hr1])
    <;> ring
  have hB : CachinElasticityMonotone.B n r = n * t ^ 2 / C n (t ^ 2) := by
    rw [hc]
    dsimp [CachinElasticityMonotone.B, CachinElasticityMonotone.T, t]
    field_simp [hr1, hq1, hq2, h1r, hn.ne']
    <;> ring
  change CachinElasticityMonotone.F n r = elasticity (D n) (D₁ n) (t ^ 2)
  unfold CachinElasticityMonotone.F elasticity D₁
  rw [hA, hB, (C_hasDerivAt n (t ^ 2) hn hz).deriv]
  have hDne' : C n (t ^ 2) + n * t ^ 2 ≠ 0 := hDne
  unfold D
  have hplus : 1 + n * t ^ 2 / C n (t ^ 2) ≠ 0 := by
    have hpos : 0 < n * t ^ 2 / C n (t ^ 2) :=
      div_pos (mul_pos hn hz.1) (C_pos n _ hn hz)
    linarith
  have hDne'' : t ^ 2 * n + C n (t ^ 2) ≠ 0 := by
    convert hDne' using 1 <;> ring
  field_simp [hcne, h1z, hn.ne', ht.1.ne', hplus, hDne']
  <;> ring_nf
  <;> (try field_simp [hDne''])
  <;> ring
end D5.S3.Entropy.RenyiCombining.CachinConvexTransport
/-! This module proves global differential inequalities for a real parameter
interval; its declarations are not finite numerical verification. -/
open Set Filter
open scoped Topology
namespace D5.S3.Entropy.RenyiCombining.CachinConvexCertificate
open CachinConvexBranch CachinConvexTransport
private theorem C_secondDeriv_neg (n : ℝ) (hn : 0 < n) (hn' : n ≤ 1 / 4) :
    ∀ z ∈ Ioo 0 1, deriv (deriv (C n)) z < 0 := by
  have hc : ContDiffOn ℝ 3 (C n) (Ioo 0 1) := fun z hz =>
    (C_contDiffAt n z hn hz).contDiffWithinAt
  have hc₁ : ContDiffOn ℝ 2 (deriv (C n)) (Ioo 0 1) :=
    hc.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hc₂ : ContDiffOn ℝ 1 (deriv (deriv (C n))) (Ioo 0 1) :=
    hc₁.deriv_of_isOpen isOpen_Ioo (by norm_num)
  apply riccati_curvature_neg_of_local (C n) (deriv (C n))
    (deriv (deriv (C n))) (deriv (deriv (deriv (C n)))) hc₁.continuousOn hc₂.continuousOn
  · intro z hz
    exact ((hc₁.differentiableOn (by norm_num)) z hz).differentiableAt
      (Ioo_mem_nhds hz.1 hz.2) |>.hasDerivAt
  · intro z hz
    exact ((hc₂.differentiableOn (by norm_num)) z hz).differentiableAt
      (Ioo_mem_nhds hz.1 hz.2) |>.hasDerivAt
  · obtain ⟨δ, hδ, hsign⟩ :=
      CachinConvexLocal.C_local_signs n hn hn'
    refine ⟨δ, hδ, ?_⟩
    intro z hz
    exact ⟨(hsign z hz).1.trans (by linarith), (hsign z hz).2⟩
  · exact C_curvature_equation n hn
private theorem D_hasDerivAt (n z : ℝ) (hn : 0 < n) (hz : z ∈ Ioo 0 1) :
    HasDerivAt (D n) (D₁ n z) z := by
  have hd := ((C_hasDerivAt n z hn hz).differentiableAt.hasDerivAt).add
    ((hasDerivAt_id z).const_mul n)
  convert hd using 1 <;> (try ext w) <;> (try dsimp [D, D₁]) <;> ring
private theorem D1_hasDerivAt (n z : ℝ) (hn : 0 < n) (hz : z ∈ Ioo 0 1) :
    HasDerivAt (D₁ n) (deriv (deriv (C n)) z) z := by
  have hc : ContDiffOn ℝ 2 (C n) (Ioo 0 1) := fun z hz =>
    (C_contDiffAt n z hn hz).contDiffWithinAt
  have hc₁ : ContDiffOn ℝ 1 (deriv (C n)) (Ioo 0 1) :=
    hc.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd : HasDerivAt (deriv (C n)) (deriv (deriv (C n)) z) z :=
    ((hc₁.differentiableOn (by norm_num)) z hz).differentiableAt
      (Ioo_mem_nhds hz.1 hz.2) |>.hasDerivAt
  convert! hd.add_const n using 1 <;> rfl
private theorem D1_neg (n : ℝ) (hn : 0 < n) (hn' : n ≤ 1 / 4) :
    ∀ z ∈ Ioo 0 1, D₁ n z < 0 := by
  have hm : StrictAntiOn (D₁ n) (Ioo 0 1) :=
    strictAntiOn_of_deriv_neg (convex_Ioo _ _)
      (fun z hz => (D1_hasDerivAt n z hn hz).continuousAt.continuousWithinAt) (by
        intro z hz
        have hz' : z ∈ Ioo 0 1 := by simpa using hz
        rw [(D1_hasDerivAt n z hn hz').deriv]
        exact C_secondDeriv_neg n hn hn' z hz')
  obtain ⟨δ, hδ, hsign⟩ :=
    CachinConvexLocal.C_local_signs n hn hn'
  intro z hz
  let l := min (z / 2) (δ / 2)
  have hl : 0 < l := lt_min (by linarith [hz.1]) (by linarith)
  have hlz : l < z := (min_le_left _ _).trans_lt (by linarith [hz.1])
  have hlδ : l < δ := (min_le_right _ _).trans_lt (by linarith)
  have hlocal : D₁ n l < 0 := by
    unfold D₁
    linarith [(hsign l ⟨hl, hlδ⟩).1]
  exact (hm ⟨hl, hlz.trans hz.2⟩ hz hlz).trans hlocal
private theorem elasticity_strictMonoOn (n : ℝ) (hn : 0 < n) (hn' : n ≤ 1 / 4) :
    StrictMonoOn (elasticity (D n) (D₁ n)) (Ioo 0 1) := by
  apply CachinConvexBranch.elasticity_strictMonoOn (D n) (D₁ n)
    (deriv (deriv (C n))) 0 1
  · intro z hz
    exact ⟨hz.1, D_pos n z hn hz⟩
  · exact fun z hz => D_hasDerivAt n z hn hz
  · exact fun z hz => D1_hasDerivAt n z hn hz
  · exact D1_neg n hn hn'
  · exact C_secondDeriv_neg n hn hn'
/-- The required elasticity monotonicity on the positive convex branch. -/
theorem antitoneOn_F (n : ℝ) (hn : 0 < n) (hn' : n ≤ 1 / 4) :
    AntitoneOn (CachinElasticityMonotone.F n) (Ioo 0 1) := by
  intro r hr s hs hrs
  rw [F_eq_denominator_elasticity n s hn hs, F_eq_denominator_elasticity n r hn hr]
  have htr := bias_mem r hr
  have hts := bias_mem s hs
  have htsr : (1 - s) / (1 + s) ≤ (1 - r) / (1 + r) := by
    apply (div_le_div_iff₀ (by linarith [hs.1]) (by linarith [hr.1])).mpr
    nlinarith
  apply (elasticity_strictMonoOn n hn hn').monotoneOn
    ⟨sq_pos_of_pos hts.1, by nlinarith [hts.1, hts.2]⟩
    ⟨sq_pos_of_pos htr.1, by nlinarith [htr.1, htr.2]⟩
  nlinarith [htr.1, hts.1]
end D5.S3.Entropy.RenyiCombining.CachinConvexCertificate
