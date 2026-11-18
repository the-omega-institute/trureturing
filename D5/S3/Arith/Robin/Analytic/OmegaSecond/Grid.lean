/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/Grid
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/Grid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite logistic grids with explicit cost and entropy errors. -/
import D5.S3.Weil.ZetaBridge.FermiMellin
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter MeasureTheory Set
open scoped Topology

namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid

/-- Occupancy at logarithmic distance u from the central cutoff. -/
def logistic (u : ℝ) : ℝ := (1 + exp u)⁻¹
/-- The logarithmic Fermi weight. -/
def fermiLog (u : ℝ) : ℝ := log (1 + exp (-u))
/-- Entropy of the logistic occupancy. -/
def entropy (u : ℝ) : ℝ := binEntropy (logistic u)

private lemma logistic_range (u : ℝ) : 0 < logistic u ∧ logistic u < 1 :=
  D5.S3.Weil.ZetaBridge.FermiMellin.fermi_bounds u

private lemma logistic_le_exp (u : ℝ) : logistic u ≤ exp (-u) :=
  D5.S3.Weil.ZetaBridge.FermiMellin.fermi_le_exp_neg u

private lemma logistic_continuous : Continuous logistic :=
  D5.S3.Weil.ZetaBridge.FermiMellin.continuous_fermi

private lemma fermiLog_deriv (u : ℝ) : HasDerivAt fermiLog (-logistic u) u := by
  have h := (((hasDerivAt_id u).neg.exp).const_add 1).log (by positivity : 1 + exp (-u) ≠ 0)
  convert h using 1
  · rfl
  · dsimp [logistic]
    rw [exp_neg]
    field_simp
    <;> ring

private lemma fermiLog_bounds (u : ℝ) : 0 ≤ fermiLog u ∧ fermiLog u ≤ exp (-u) := by
  constructor
  · exact log_nonneg (by linarith [exp_pos (-u)])
  · have h := log_le_sub_one_of_pos (by positivity : 0 < 1 + exp (-u))
    simpa [fermiLog] using h

private lemma entropy_identity (u : ℝ) : entropy u = fermiLog u + u * logistic u := by
  have he := exp_pos u
  have hp : 1 - logistic u = exp u / (1 + exp u) := by
    dsimp [logistic]
    field_simp
    <;> ring
  have hn : 1 + exp u ≠ 0 := by positivity
  have hj : fermiLog u = log (1 + exp u) - u := by
    dsimp [fermiLog]
    rw [exp_neg, show 1 + (exp u)⁻¹ = (1 + exp u) / exp u by field_simp; ring,
      log_div hn he.ne', log_exp]
  rw [entropy, binEntropy, hp, logistic, inv_inv, log_inv, log_div he.ne' hn, log_exp, hj]
  field_simp
  <;> ring

private lemma fermi_real_one : IntegrableOn logistic (Ioi 0) ∧
    (∫ u in Ioi (0 : ℝ), logistic u) = log 2 := by
  have hi := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_integrable
    1 (by norm_num) 1 (by norm_num)
  have he := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_at_one 1 (by norm_num)
  have hp (u : ℝ) : ((u : ℂ) ^ ((1 : ℂ) - 1) / ((exp (1 * u) : ℂ) + 1)).re = logistic u := by
    norm_num only [sub_self, Complex.cpow_zero, one_mul]
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_div, Complex.ofReal_re]
    simp only [logistic, one_div, add_comm]
  refine ⟨hi.re.congr (Eventually.of_forall hp), ?_⟩
  calc
    (∫ u in Ioi (0 : ℝ), logistic u) = ∫ u in Ioi (0 : ℝ),
        ((u : ℂ) ^ ((1 : ℂ) - 1) / ((exp (1 * u) : ℂ) + 1)).re := by
      exact integral_congr_ae (Eventually.of_forall (fun u => (hp u).symm))
    _ = _ := integral_re hi
    _ = log 2 := by rw [he]; simp only [Complex.ofReal_one, div_one, Complex.ofReal_re]

private lemma fermi_real_two : IntegrableOn (fun u => u * logistic u) (Ioi 0) ∧
    (∫ u in Ioi (0 : ℝ), u * logistic u) = π ^ 2 / 12 := by
  have hi := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_integrable
    1 (by norm_num) 2 (by norm_num)
  have he := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_eq_of_ne_one
    1 (by norm_num) 2 (by norm_num) (by norm_num)
  have hp (u : ℝ) : ((u : ℂ) ^ ((2 : ℂ) - 1) / ((exp (1 * u) : ℂ) + 1)).re =
      u * logistic u := by
    norm_num only [show (2 : ℂ) - 1 = 1 by norm_num, Complex.cpow_one, one_mul]
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_div, Complex.ofReal_re]
    simp only [logistic, div_eq_mul_inv, add_comm]
  refine ⟨hi.re.congr (Eventually.of_forall hp), ?_⟩
  calc
    (∫ u in Ioi (0 : ℝ), u * logistic u) = ∫ u in Ioi (0 : ℝ),
        ((u : ℂ) ^ ((2 : ℂ) - 1) / ((exp (1 * u) : ℂ) + 1)).re := by
      exact integral_congr_ae (Eventually.of_forall (fun u => (hp u).symm))
    _ = _ := integral_re hi
    _ = π ^ 2 / 12 := by
      rw [he, show Complex.Gamma 2 = 1 by simpa using Complex.Gamma_nat_eq_factorial 1,
        riemannZeta_two, show (1 : ℂ) - 2 = -1 by norm_num, Complex.cpow_neg_one]
      norm_num [Complex.div_re, Complex.mul_re, ← Complex.ofReal_pow]
      <;> ring

private lemma exp_integrable : IntegrableOn (fun u : ℝ => exp (-u)) (Ioi 0) := by
  simpa using integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0

private lemma fermiLog_integrable : IntegrableOn fermiLog (Ioi 0) := by
  apply exp_integrable.mono'
    ((continuous_iff_continuousAt.mpr (fun u => (fermiLog_deriv u).continuousAt)).aestronglyMeasurable)
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (fermiLog_bounds u).1]
  exact (fermiLog_bounds u).2

private lemma mul_exp_limit : Tendsto (fun u : ℝ => u * exp (-u)) atTop (𝓝 0) := by
  simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 (by norm_num)

private lemma mul_fermiLog_limit : Tendsto (fun u : ℝ => u * fermiLog u) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ mul_exp_limit
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact mul_nonneg hu (fermiLog_bounds u).1
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact mul_le_mul_of_nonneg_left (fermiLog_bounds u).2 hu

private lemma integral_fermiLog : (∫ u in Ioi (0 : ℝ), fermiLog u) = π ^ 2 / 12 := by
  have hd (u : ℝ) : HasDerivAt (fun v => v * fermiLog v)
      (fermiLog u - u * logistic u) u := by
    convert (hasDerivAt_id u).mul (fermiLog_deriv u) using 1 <;> ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u _ => hd u) (fermiLog_integrable.sub fermi_real_two.1) mul_fermiLog_limit
  rw [integral_sub fermiLog_integrable fermi_real_two.1, fermi_real_two.2] at h
  simp only [zero_mul, sub_zero] at h
  linarith

private lemma entropy_continuous : Continuous entropy :=
  binEntropy_continuous.comp logistic_continuous

private lemma entropy_integral : IntegrableOn entropy (Ioi 0) ∧
    (∫ u in Ioi (0 : ℝ), entropy u) = π ^ 2 / 6 := by
  refine ⟨(fermiLog_integrable.add fermi_real_two.1).congr
    (Eventually.of_forall (fun u => (entropy_identity u).symm)), ?_⟩
  simp_rw [entropy_identity]
  rw [integral_add fermiLog_integrable fermi_real_two.1, integral_fermiLog, fermi_real_two.2]
  ring

private lemma logistic_antitone : Antitone logistic := by
  intro u v huv
  exact inv_anti₀ (by positivity) (add_le_add_right (exp_le_exp.mpr huv) 1)

private lemma entropy_antitone : AntitoneOn entropy (Ici 0) := by
  intro u hu v hv huv
  apply binEntropy_strictMonoOn.monotoneOn
  · exact ⟨(logistic_range v).1.le, by
      have h := logistic_antitone hv
      norm_num [logistic] at h
      simpa only [logistic, one_div] using h⟩
  · exact ⟨(logistic_range u).1.le, by
      have h := logistic_antitone hu
      norm_num [logistic] at h
      simpa only [logistic, one_div] using h⟩
  · exact logistic_antitone huv

private lemma envelope_integrable :
    IntegrableOn (fun u : ℝ => (1 + u) * exp (-u)) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => u * exp (-u)) (Ioi 0) := by
    have h := GammaIntegral_convergent (s := 2) (by norm_num)
    norm_num at h
    simpa only [mul_comm] using h
  apply (exp_integrable.add h).congr
  filter_upwards with u
  change exp (-u) + u * exp (-u) = (1 + u) * exp (-u)
  ring

private lemma envelope_tail {U : ℝ} (hU : 0 ≤ U) :
    (∫ u in Ioi U, (1 + u) * exp (-u)) = (U + 2) * exp (-U) := by
  have hi := envelope_integrable.mono_set (Ioi_subset_Ioi hU)
  have hl : Tendsto (fun u : ℝ => -(u + 2) * exp (-u)) atTop (𝓝 0) := by
    have he : Tendsto (fun u : ℝ => exp (-u)) atTop (𝓝 0) :=
      tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    simpa [add_mul, neg_add, neg_mul] using (mul_exp_limit.add (he.const_mul 2)).neg
  have hd (u : ℝ) : HasDerivAt (fun v : ℝ => -(v + 2) * exp (-v))
      ((1 + u) * exp (-u)) u := by
    convert (((hasDerivAt_id u).add_const 2).neg).mul ((hasDerivAt_id u).neg.exp) using 1
    all_goals first | (funext v; dsimp; ring) | ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun u _ => hd u) hi hl
  convert h using 1 <;> ring

private lemma entropy_truncated {U : ℝ} (hU : 0 ≤ U) :
    π ^ 2 / 6 - (U + 2) * exp (-U) ≤ ∫ u in (0 : ℝ)..U, entropy u := by
  have hb : ∀ᵐ u ∂(volume.restrict (Ioi U)), entropy u ≤ (1 + u) * exp (-u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [entropy_identity, add_mul, one_mul]
    exact add_le_add (fermiLog_bounds u).2
      (mul_le_mul_of_nonneg_left (logistic_le_exp u) (hU.trans hu.le))
  have he := integral_mono_ae
    (entropy_integral.1.mono_set (Ioi_subset_Ioi hU))
    (envelope_integrable.mono_set (Ioi_subset_Ioi hU)) hb
  rw [envelope_tail hU] at he
  rw [← intervalIntegral.integral_Ioi_sub_Ioi entropy_integral.1 hU, entropy_integral.2]
  linarith

/-- A finite uniform grid, chosen before the asymptotic parameter varies. -/
structure Mesh where
  U : ℝ
  n : ℕ
  U_pos : 0 < U
  n_pos : 0 < n

def Mesh.step (G : Mesh) : ℝ := G.U / G.n
def Mesh.node (G : Mesh) (i : ℕ) : ℝ := i * G.step
def Mesh.cost (G : Mesh) : ℝ :=
  2 * ∑ i ∈ Finset.range G.n, G.step * G.node (i + 1) * logistic (G.node (i + 1))
def Mesh.mass (G : Mesh) : ℝ :=
  2 * ∑ i ∈ Finset.range G.n, G.step * entropy (G.node (i + 1))

lemma step_pos (G : Mesh) : 0 < G.step := by
  exact div_pos G.U_pos (by exact_mod_cast G.n_pos)
private lemma node_nonneg (G : Mesh) (i : ℕ) : 0 ≤ G.node i := by
  exact mul_nonneg (Nat.cast_nonneg i) (step_pos G).le
lemma node_step (G : Mesh) (i : ℕ) : G.node (i+1) - G.node i = G.step := by
  simp [Mesh.node, Nat.cast_add, Nat.cast_one]; ring
lemma node_end (G : Mesh) : G.node G.n = G.U := by
  dsimp [Mesh.node, Mesh.step]
  exact mul_div_cancel₀ _ (by exact_mod_cast G.n_pos.ne')
lemma node_zero (G : Mesh) : G.node 0 = 0 := by simp [Mesh.node]

private lemma cell_cost (G : Mesh) (i : ℕ) :
    G.step * G.node (i+1) * logistic (G.node (i+1)) ≤
      (∫ u in G.node i..G.node (i+1), u * logistic u) +
      G.step * ∫ u in G.node i..G.node (i+1), logistic u := by
  have hab : G.node i ≤ G.node (i+1) := by linarith [step_pos G, node_step G i]
  have hq := logistic_continuous.intervalIntegrable (μ := volume) (G.node i) (G.node (i+1))
  have huq : IntervalIntegrable (fun u : ℝ => u * logistic u) volume
      (G.node i) (G.node (i+1)) :=
    (continuous_id.mul logistic_continuous).intervalIntegrable (μ := volume) _ _
  have h : (∫ _ in G.node i..G.node (i+1),
      G.node (i+1) * logistic (G.node (i+1))) ≤
      ∫ u in G.node i..G.node (i+1), u * logistic u + G.step * logistic u := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hab intervalIntegrable_const
      (huq.add (hq.const_mul G.step))
    intro u hu
    have hqu := logistic_antitone hu.2.le
    have hbu : G.node (i+1) ≤ u + G.step := by linarith [node_step G i, hu.1]
    calc
      G.node (i+1) * logistic (G.node (i+1)) ≤ G.node (i+1) * logistic u :=
        mul_le_mul_of_nonneg_left hqu (node_nonneg G _)
      _ ≤ (u + G.step) * logistic u :=
        mul_le_mul_of_nonneg_right hbu (logistic_range u).1.le
      _ = u * logistic u + G.step * logistic u := by ring
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add huq (hq.const_mul _),
    intervalIntegral.integral_const_mul, node_step, smul_eq_mul] at h
  simpa [mul_assoc] using h

private lemma cell_entropy (G : Mesh) (i : ℕ) :
    (∫ u in G.node i..G.node (i+1), entropy u) -
      G.step * entropy (G.node (i+1)) ≤
      G.step * (entropy (G.node i) - entropy (G.node (i+1))) := by
  have hab : G.node i ≤ G.node (i+1) := by linarith [step_pos G, node_step G i]
  have h : (∫ u in G.node i..G.node (i+1), entropy u) ≤
      ∫ _ in G.node i..G.node (i+1), entropy (G.node i) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hab
      (entropy_continuous.intervalIntegrable (μ := volume) _ _) intervalIntegrable_const
    intro u hu
    exact entropy_antitone (node_nonneg G i) ((node_nonneg G i).trans hu.1.le) hu.1.le
  rw [intervalIntegral.integral_const, node_step, smul_eq_mul] at h
  linarith

private lemma truncated_le {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    (hp : ∀ u, 0 ≤ u → 0 ≤ f u) {U : ℝ} (hU : 0 ≤ U) :
    (∫ u in (0 : ℝ)..U, f u) ≤ ∫ u in Ioi (0 : ℝ), f u := by
  rw [intervalIntegral.integral_of_le hU]
  apply setIntegral_mono_set hf
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu using hp u hu.le
  · exact Eventually.of_forall (fun u hu => hu.1)

/-- Finite endpoint sampling controls both cost and entropy, with explicit mesh and tail errors. -/
theorem grid_bounds (G : Mesh) :
    G.cost ≤ π ^ 2 / 6 + 2 * G.step * log 2 ∧
    π ^ 2 / 3 - 2 * (G.U + 2) * exp (-G.U) - 2 * G.step * log 2 ≤ G.mass := by
  have hq := intervalIntegral.sum_integral_adjacent_intervals
    (a := G.node) (n := G.n) (f := logistic)
    (fun _ _ => logistic_continuous.intervalIntegrable (μ := volume) _ _)
  have huq := intervalIntegral.sum_integral_adjacent_intervals
    (a := G.node) (n := G.n) (f := fun u => u * logistic u)
    (fun _ _ => (continuous_id.mul logistic_continuous).intervalIntegrable (μ := volume) _ _)
  have hf := intervalIntegral.sum_integral_adjacent_intervals
    (a := G.node) (n := G.n) (f := entropy)
    (fun _ _ => entropy_continuous.intervalIntegrable (μ := volume) _ _)
  rw [node_zero, node_end] at hq huq hf
  constructor
  · have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range G.n) => cell_cost G i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hq, huq] at h
    have h₁ := truncated_le fermi_real_two.1
      (fun u hu => mul_nonneg hu (logistic_range u).1.le) G.U_pos.le
    have h₂ := truncated_le fermi_real_one.1 (fun u _ => (logistic_range u).1.le) G.U_pos.le
    rw [fermi_real_two.2] at h₁
    rw [fermi_real_one.2] at h₂
    dsimp [Mesh.cost]
    nlinarith [mul_le_mul_of_nonneg_left h₂ (step_pos G).le]
  · have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range G.n) => cell_entropy G i)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_range_sub', node_zero, node_end, hf] at h
    have hfU : 0 ≤ entropy G.U :=
      binEntropy_nonneg (logistic_range G.U).1.le (logistic_range G.U).2.le
    have h0 : entropy 0 = log 2 := by
      rw [entropy, logistic, exp_zero, show (1 : ℝ) + 1 = 2 by norm_num]
      exact binEntropy_two_inv
    rw [h0] at h
    have ht := entropy_truncated G.U_pos.le
    dsimp [Mesh.mass]
    rw [← Finset.mul_sum]
    nlinarith [mul_nonneg (step_pos G).le hfU]

/-- A fixed grid achieves any prescribed positive cost slack and entropy loss. -/
theorem exists_good_grid {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ G : Mesh, G.cost ≤ (π ^ 2 / 6) * (1 + η / 2) ∧
      π ^ 2 / 3 - ρ ≤ G.mass := by
  have he : Tendsto (fun u : ℝ => exp (-u)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have ht : Tendsto (fun u : ℝ => 2 * (u + 2) * exp (-u)) atTop (𝓝 0) := by
    simpa [add_mul, mul_add, mul_assoc] using (mul_exp_limit.add (he.const_mul 2)).const_mul 2
  obtain ⟨U, hU, htU⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    (ht.eventually_lt_const (by linarith : (0 : ℝ) < ρ / 2))).exists
  have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
  let d := min ((π ^ 2 / 6) * η / (4 * log 2)) (ρ / (4 * log 2))
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (U / d))
  have hn1 : 0 < n := by
    have hnR : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
    exact_mod_cast (lt_trans zero_lt_one hnR)
  let G : Mesh := ⟨U, n, by linarith, hn1⟩
  have hs : G.step ≤ d := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    apply (div_le_iff₀ hnR).mpr
    have h := (div_lt_iff₀ hd).mp ((le_max_right _ _).trans_lt hn)
    simpa [mul_comm] using h.le
  have hs₁ : 2 * G.step * log 2 ≤ (π ^ 2 / 6) * η / 2 := by
    have h := hs.trans (min_le_left _ _)
    have hd' : 0 < 4 * log (2 : ℝ) := by positivity
    have h := (le_div_iff₀ hd').mp h
    nlinarith
  have hs₂ : 2 * G.step * log 2 ≤ ρ / 2 := by
    have h := hs.trans (min_le_right _ _)
    have hd' : 0 < 4 * log (2 : ℝ) := by positivity
    have h := (le_div_iff₀ hd').mp h
    nlinarith
  obtain ⟨hc, hm⟩ := grid_bounds G
  refine ⟨G, ?_, ?_⟩
  · nlinarith
  · change π ^ 2 / 3 - 2 * (U + 2) * exp (-U) - 2 * G.step * log 2 ≤ G.mass at hm
    linarith

end D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid
