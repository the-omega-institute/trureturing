/- GID: D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling
   mirror-E: none(waiver:direct-Lean-proof)
   anchors: []
   utility: none
   digest: The logarithmic permanent rate converges to its closed cotangent form. -/

/- Mathematical classification:
   hasDerivAt_quadLogPrimitive: proof_shape: bind-only; escape_witness: none; consumer: integral_quadLog
   continuous_quadLog: proof_shape: bind-only; escape_witness: none; consumer: integral_quadLog, chord_log_integral
   integral_quadLog: proof_shape: bind-only; escape_witness: none; consumer: integral_trig_quadLog
   integral_trig_quadLog: proof_shape: bind-only; escape_witness: none; consumer: chord_log_integral
   q_norm: proof_shape: bind-only; escape_witness: none; consumer: logIntegrand_continuousOn, rate_eq_riemann_of_product
   q_ne_neg_one: proof_shape: bind-only; escape_witness: none; consumer: logIntegrand_continuousOn, rate_eq_riemann_of_product
   unit_chord_ne_zero: proof_shape: bind-only; escape_witness: none; consumer: logIntegrand_continuousOn, log_productValue
   logIntegrand_continuousOn: proof_shape: bind-only; escape_witness: none; consumer: logRiemann_limit
   chord_normSq: proof_shape: bind-only; escape_witness: none; consumer: chord_log_norm
   chord_log_norm: proof_shape: bind-only; escape_witness: none; consumer: chord_log_integral
   chord_log_integral: proof_shape: bind-only; escape_witness: none; consumer: logIntegrand_integral_left
   q_complement: proof_shape: bind-only; escape_witness: none; consumer: logIntegrand_complement
   logIntegrand_complement: proof_shape: bind-only; escape_witness: none; consumer: logIntegral_evaluation
   logIntegrand_integral_left: proof_shape: bind-only; escape_witness: none; consumer: logIntegral_evaluation
   logIntegral_evaluation: proof_shape: bind-only; escape_witness: none; consumer: result3
   leftRiemann_error_le: proof_shape: bind-only; escape_witness: none; consumer: continuous_leftRiemann_tendsto
   continuous_leftRiemann_tendsto: proof_shape: bind-only; escape_witness: none; consumer: logRiemann_limit
   logRiemann_limit: proof_shape: bind-only; escape_witness: none; consumer: result3
   product_normalized: proof_shape: bind-only; escape_witness: none; consumer: log_productValue
   fin_fraction_mem_Icc: proof_shape: bind-only; escape_witness: none; consumer: log_productValue
   log_productValue: proof_shape: bind-only; escape_witness: none; consumer: rate_eq_riemann_of_product
   rate_eq_riemann_of_product: proof_shape: bind-only; escape_witness: none; consumer: problem3_nonmidpoint_of_components
   problem3_nonmidpoint_of_components: proof_shape: bind-only; escape_witness: none; consumer: result3
   midpoint_log_norm_product: proof_shape: bind-only; escape_witness: none; consumer: midpoint_rate_of_product
   midpoint_rate_of_product: proof_shape: bind-only; escape_witness: none; consumer: midpoint_rate_tendsto_of_product
   midpoint_reciprocal_tendsto: proof_shape: bind-only; escape_witness: none; consumer: midpointLogRatio_tendsto, midpoint_rate_tendsto_of_product
   midpointLogRatio_tendsto: proof_shape: bind-only; escape_witness: none; consumer: midpoint_rate_tendsto_of_product
   midpoint_rate_tendsto_of_product: proof_shape: bind-only; escape_witness: none; consumer: result3
   result3: proof_shape: content; escape_witness: CycleGeodesic.gaudin_permanent; consumer: none
   escape_witness: CycleGeodesic.gaudin_permanent: ∀ n : ℕ, ∀ x y : Fin n → ℂ, Function.Injective x → (∀ i j, x i ≠ y j) → (gaudin x y).det = (cauchy x y).permanent
   admission_basis: open-problem-resolution (#13612; Proved)
   Direct frozen dependencies: none at the immutable origin/dev baseline.
   Information-escape registration is paused under CLAUDE.md section 3.9. -/

import D5.S3.Combinatorics.Permanental.CycleGeodesic.CycleGeodesicMidpoint

noncomputable section
open scoped BigOperators Topology
open Filter Finset Polynomial Matrix Equiv Real
namespace CycleGeodesic

def delta (t : ℝ) : ℝ := min t (1 - t)

def rate (n : ℕ) (t : ℝ) : ℝ := -(1 / (n : ℝ)) * Real.log ‖(gamma n t).permanent‖

def universal (t : ℝ) : ℝ := 1 - Real.pi * delta t * Real.cot (Real.pi * delta t)

def claim3 : Prop :=
  (∀ t : ℝ, 0 < t → t < 1 → t ≠ 1 / 2 →
    Tendsto (fun n : ℕ => rate n t) atTop (𝓝 (universal t))) ∧
  Tendsto (fun m : ℕ => rate (2 * m + 1) (1 / 2)) atTop (𝓝 1)

private def logIntegrand (t x : ℝ) : ℝ := Real.log ‖(1 - x : ℝ) + (x : ℂ) * (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I))‖

private def quadLogPrimitive (a b x : ℝ) : ℝ :=
  x * Real.log (a ^ 2 + b ^ 2 * x ^ 2) - 2 * x +
    2 * a / b * Real.arctan (b * x / a)

private lemma hasDerivAt_quadLogPrimitive {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    HasDerivAt (quadLogPrimitive a b) (Real.log (a ^ 2 + b ^ 2 * x ^ 2)) x := by
  have hz : a ^ 2 + b ^ 2 * x ^ 2 ≠ 0 := by positivity
  have hq := (((hasDerivAt_id x).pow 2).const_mul (b ^ 2)).const_add (a ^ 2)
  have h1 := (hasDerivAt_id x).mul (hq.log hz)
  have h2 := (hasDerivAt_id x).const_mul 2
  have h3 := ((((hasDerivAt_id x).const_mul b).div_const a).arctan).const_mul (2 * a / b)
  convert! (h1.sub h2).add h3 using 1
  simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, one_mul]
  field_simp [ha.ne', hb.ne', hz]
  ring

private lemma continuous_quadLog {a b : ℝ} (ha : 0 < a) :
    Continuous (fun x : ℝ => Real.log (a ^ 2 + b ^ 2 * x ^ 2)) := by
  apply Continuous.log
  · fun_prop
  · intro x
    positivity

private lemma integral_quadLog {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in (0 : ℝ)..1, Real.log (a ^ 2 + b ^ 2 * x ^ 2)) =
      Real.log (a ^ 2 + b ^ 2) - 2 + 2 * a / b * Real.arctan (b / a) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_quadLogPrimitive ha hb x)
    ((continuous_quadLog (b := b) ha).intervalIntegrable 0 1)
  simpa [quadLogPrimitive] using h

private lemma integral_trig_quadLog {α : ℝ} (hα0 : 0 < α) (hα1 : α < Real.pi / 2) :
    (1 / 2 : ℝ) * (∫ x in (0 : ℝ)..1,
      Real.log (Real.cos α ^ 2 + Real.sin α ^ 2 * x ^ 2)) =
      α * Real.cot α - 1 := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα1⟩
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
  rw [integral_quadLog hc hs, Real.cos_sq_add_sin_sq, Real.log_one,
    ← Real.tan_eq_sin_div_cos, Real.arctan_tan (by linarith [Real.pi_pos]) hα1,
    Real.cot_eq_cos_div_sin]
  ring

private lemma q_norm (t : ℝ) : ‖(Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I))‖ = 1 := by
  simp [Complex.norm_exp]

private lemma q_ne_neg_one {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (ht : t ≠ 1 / 2) :
    (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) ≠ -1 := by
  intro h
  have hexp : Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) =
      Complex.exp (Real.pi * Complex.I) := by simpa [Complex.exp_pi_mul_I] using h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have him := congrArg Complex.im hk
  simp at him
  have htk : t = (k : ℝ) + 1 / 2 := by nlinarith [Real.pi_pos]
  have hklo : (-1 : ℤ) < k := by exact_mod_cast (show (-1 : ℝ) < k by linarith)
  have hkhi : k < (1 : ℤ) := by exact_mod_cast (show (k : ℝ) < 1 by linarith)
  have hk0 : k = 0 := by omega
  exact ht (by simpa [hk0] using htk)

private lemma unit_chord_ne_zero {z : ℂ} (hz : ‖z‖ = 1) (hzm : z ≠ -1)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : (1 - x : ℝ) + (x : ℂ) * z ≠ 0 := by
  intro h
  have heq : (x : ℂ) * z = -((1 - x : ℝ) : ℂ) := by linear_combination h
  have hn := congrArg norm heq
  simp only [norm_mul, hz, mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hx.1, abs_of_nonneg (sub_nonneg.mpr hx.2)] at hn
  have hxhalf : x = 1 / 2 := by linarith
  apply hzm
  rw [hxhalf] at heq
  norm_num at heq
  linear_combination 2 * heq

private lemma logIntegrand_continuousOn {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (ht : t ≠ 1 / 2) :
    ContinuousOn (logIntegrand t) (Set.Icc (0 : ℝ) 1) := by
  apply ContinuousOn.log
  · fun_prop
  · intro x hx
    exact norm_ne_zero_iff.mpr (unit_chord_ne_zero (q_norm t) (q_ne_neg_one ht0 ht1 ht) hx)

private lemma chord_normSq (α x : ℝ) :
    Complex.normSq ((1 - x : ℝ) + (x : ℂ) *
      Complex.exp ((2 * α : ℝ) * Complex.I)) =
      Real.cos α ^ 2 + Real.sin α ^ 2 * (2 * x - 1) ^ 2 := by
  have htrig := Real.sin_sq_add_cos_sq α
  have heq : 1 - x + x * (Real.cos α ^ 2 - Real.sin α ^ 2) =
      Real.cos α ^ 2 + (1 - 2 * x) * Real.sin α ^ 2 := by
    linear_combination -(1 - x) * htrig
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_add, add_zero, mul_one,
    Real.exp_zero, one_mul, Real.cos_two_mul, Real.sin_two_mul]
  rw [show (2 * Real.cos α ^ 2 - 1) = Real.cos α ^ 2 - Real.sin α ^ 2 by linarith, heq]
  calc
    _ = (Real.sin α ^ 2 + Real.cos α ^ 2) *
        (Real.cos α ^ 2 + Real.sin α ^ 2 * (2 * x - 1) ^ 2) := by ring
    _ = _ := by rw [htrig, one_mul]

private lemma chord_log_norm (α x : ℝ) :
    Real.log ‖((1 - x : ℝ) + (x : ℂ) * Complex.exp ((2 * α : ℝ) * Complex.I))‖ =
      (1 / 2 : ℝ) * Real.log (Real.cos α ^ 2 + Real.sin α ^ 2 * (2 * x - 1) ^ 2) := by
  rw [Complex.norm_def, chord_normSq, Real.log_sqrt (by positivity)]
  ring

private lemma chord_log_integral {α : ℝ} (hα0 : 0 < α) (hα1 : α < Real.pi / 2) :
    (∫ x in (0 : ℝ)..1, Real.log ‖((1 - x : ℝ) + (x : ℂ) *
      Complex.exp ((2 * α : ℝ) * Complex.I))‖) = α * Real.cot α - 1 := by
  simp_rw [chord_log_norm]
  rw [intervalIntegral.integral_const_mul]
  have hchange := intervalIntegral.integral_comp_mul_sub
    (fun u : ℝ => Real.log (Real.cos α ^ 2 + Real.sin α ^ 2 * u ^ 2))
    (a := 0) (b := 1) (c := 2) (by norm_num) 1
  norm_num at hchange
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα1⟩
  have hcont := continuous_quadLog (a := Real.cos α) (b := Real.sin α) hc
  have heven : (∫ u in (-1 : ℝ)..1, Real.log (Real.cos α ^ 2 + Real.sin α ^ 2 * u ^ 2)) =
      2 * (∫ u in (0 : ℝ)..1, Real.log (Real.cos α ^ 2 + Real.sin α ^ 2 * u ^ 2)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (-1) 0) (hcont.intervalIntegrable 0 1)]
    have hs := intervalIntegral.integral_comp_neg
      (fun u : ℝ => Real.log (Real.cos α ^ 2 + Real.sin α ^ 2 * u ^ 2)) (a := 0) (b := 1)
    simp only [neg_zero, neg_sq] at hs
    linarith
  have hi := integral_trig_quadLog hα0 hα1
  rw [heven] at hchange
  linarith

private lemma q_complement (t : ℝ) : (Complex.exp ((2 * Real.pi * (1 - t) : ℝ) * Complex.I)) = (starRingEnd ℂ) ((Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I))) := by
  rw [← Complex.exp_conj]
  have heq : ((2 * Real.pi * (1 - t) : ℝ) : ℂ) * Complex.I =
      2 * Real.pi * Complex.I + (starRingEnd ℂ) (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [heq, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]

private lemma logIntegrand_complement (t x : ℝ) : logIntegrand (1 - t) x = logIntegrand t x := by
  unfold logIntegrand
  rw [q_complement]
  have hc : ((1 - x : ℝ) : ℂ) + (x : ℂ) * (starRingEnd ℂ) ((Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I))) =
      (starRingEnd ℂ) (((1 - x : ℝ) : ℂ) + (x : ℂ) * (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I))) := by simp
  rw [hc, Complex.norm_conj]

private lemma logIntegrand_integral_left {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    (∫ x in (0 : ℝ)..1, logIntegrand t x) =
      Real.pi * t * Real.cot (Real.pi * t) - 1 := by
  have hα0 : 0 < Real.pi * t := mul_pos Real.pi_pos ht0
  have hα1 : Real.pi * t < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hi := chord_log_integral hα0 hα1
  have hf : (logIntegrand t) = (fun x : ℝ => Real.log ‖((1 - x : ℝ) + (x : ℂ) *
      Complex.exp ((2 * (Real.pi * t) : ℝ) * Complex.I))‖) := by
    ext x
    unfold logIntegrand
    congr 4
    ring
  rw [hf]
  exact hi

private lemma logIntegral_evaluation : (∀ t : ℝ, 0 < t → t < 1 → t ≠ 1 / 2 →
  -(∫ x in (0 : ℝ)..1, logIntegrand t x) = universal t) := by
  intro t ht0 ht1 ht
  unfold universal delta
  by_cases hh : t < 1 / 2
  · rw [min_eq_left (by linarith), logIntegrand_integral_left ht0 hh]
    ring
  · have htc0 : 0 < 1 - t := by linarith
    have htc1 : 1 - t < 1 / 2 := by
      rcases lt_or_eq_of_le (le_of_not_gt hh) with h | h
      · linarith
      · exact False.elim (ht h.symm)
    have h := logIntegrand_integral_left htc0 htc1
    simp_rw [logIntegrand_complement] at h
    rw [min_eq_right (by linarith), h]
    ring

private lemma leftRiemann_error_le {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    {ε d : ℝ} (hε : 0 ≤ ε) (hd : 0 < d)
    (hm : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      dist x y < d → dist (f x) (f y) ≤ ε)
    {n : ℕ} (hn : n ≠ 0) (hmesh : 1 / (n : ℝ) < d) :
    ‖(1 / (n : ℝ)) * ∑ k : Fin n, f ((k : ℝ) / n) - ∫ x in (0 : ℝ)..1, f x‖ ≤ ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  let a : ℕ → ℝ := fun k => (k : ℝ) / n
  have hstep (k : ℕ) : a (k + 1) - a k = 1 / (n : ℝ) := by
    dsimp [a]
    push_cast
    ring
  have hab (k : ℕ) : a k ≤ a (k + 1) := by
    have h := hstep k
    linarith [show 0 < 1 / (n : ℝ) by positivity]
  have hsub (k : ℕ) (hk : k < n) : Set.Icc (a k) (a (k + 1)) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    have hk0 : 0 ≤ a k := by dsimp [a]; positivity
    have hk1 : a (k + 1) ≤ 1 := by
      dsimp [a]
      apply (div_le_one hnR).2
      exact_mod_cast (Nat.succ_le_of_lt hk)
    exact ⟨hk0.trans hx.1, hx.2.trans hk1⟩
  have hint (k : ℕ) (hk : k < n) : IntervalIntegrable f MeasureTheory.volume (a k) (a (k + 1)) :=
    (hf.mono (hsub k hk)).intervalIntegrable_of_Icc (hab k)
  have htel := intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : a 0 = 0 := by simp [a]
  have han : a n = 1 := by simp [a, hnR.ne']
  rw [ha0, han] at htel
  have herr (k : ℕ) (hk : k < n) :
      ‖(1 / (n : ℝ)) * f (a k) - ∫ x in a k..a (k + 1), f x‖ ≤ ε / n := by
    have heq : (1 / (n : ℝ)) * f (a k) - (∫ x in a k..a (k + 1), f x) =
        ∫ x in a k..a (k + 1), f (a k) - f x := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const) (hint k hk),
        intervalIntegral.integral_const, smul_eq_mul, hstep]
    rw [heq]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a k) (b := a (k + 1))
      (C := ε) (f := fun x => f (a k) - f x) ?_
    · simpa [hstep, abs_of_pos (show 0 < 1 / (n : ℝ) by positivity), div_eq_mul_inv] using h
    intro x hx
    rw [Set.uIoc_of_le (hab k)] at hx
    have hx' : x ∈ Set.Icc (a k) (a (k + 1)) := ⟨hx.1.le, hx.2⟩
    have hk' : a k ∈ Set.Icc (0 : ℝ) 1 := hsub k hk ⟨le_rfl, hab k⟩
    have hdist : dist (a k) x < d := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hx'.1] : a k - x ≤ 0)]
      have h := hstep k
      linarith [hx'.2]
    simpa [dist_eq_norm] using hm (a k) hk' x (hsub k hk hx') hdist
  rw [show (∑ k : Fin n, f ((k : ℝ) / n)) = ∑ k ∈ range n, f ((k : ℝ) / n) from
    Fin.sum_univ_eq_sum_range (fun k => f ((k : ℝ) / n)) n,
    Finset.mul_sum, ← htel, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖1 / (n : ℝ) * f (a k) - ∫ x in a k..a (k + 1), f x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, ε / (n : ℝ) :=
      Finset.sum_le_sum (fun k hk => herr k (Finset.mem_range.mp hk))
    _ = ε := by simp [hnR.ne']; field_simp

private lemma continuous_leftRiemann_tendsto {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∑ k : Fin n, f ((k : ℝ) / n))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hf
  obtain ⟨d, hd, hm⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 2) (by positivity)
  have ht : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < d :=
    (tendsto_one_div_atTop_nhds_zero_nat.eventually (gt_mem_nhds hd))
  obtain ⟨N, hN⟩ := eventually_atTop.mp ht
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have h := leftRiemann_error_le hf (by positivity : 0 ≤ ε / 2) hd
    (fun x hx y hy hxy => (hm x hx y hy hxy).le) hn0 (hN n (by omega))
  rw [dist_eq_norm]
  exact h.trans_lt (by linarith)

private lemma logRiemann_limit : (∀ t : ℝ, 0 < t → t < 1 → t ≠ 1 / 2 →
  Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
    ∑ k : Fin n, logIntegrand t ((k : ℝ) / n)) atTop
    (𝓝 (-(∫ x in (0 : ℝ)..1, logIntegrand t x)))) := by
  intro t ht0 ht1 ht
  have h := continuous_leftRiemann_tendsto (logIntegrand_continuousOn ht0 ht1 ht)
  simpa [neg_mul] using h.neg

private lemma product_normalized {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    productValue n z = ∏ k : Fin n,
      ((1 - (k : ℝ) / n : ℝ) + ((k : ℝ) / n : ℝ) * z : ℂ) := by
  unfold productValue
  rw [show (n : ℂ)⁻¹ ^ n = ∏ _ : Fin n, (n : ℂ)⁻¹ by simp,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp

private lemma fin_fraction_mem_Icc {n : ℕ} (hn : n ≠ 0) (k : Fin n) :
    (k : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  constructor
  · positivity
  · exact (div_le_one hnR).mpr (by exact_mod_cast (Nat.le_of_lt k.isLt))

private lemma log_productValue {n : ℕ} (hn : n ≠ 0) {z : ℂ} (hz : ‖z‖ = 1) (hzm : z ≠ -1) :
    Real.log ‖productValue n z‖ =
      ∑ k : Fin n, Real.log ‖((1 - (k : ℝ) / n : ℝ) + ((k : ℝ) / n : ℝ) * z : ℂ)‖ := by
  rw [product_normalized hn, norm_prod]
  apply Real.log_prod
  intro k hk
  exact norm_ne_zero_iff.mpr (unit_chord_ne_zero hz hzm (fin_fraction_mem_Icc hn k))

private lemma rate_eq_riemann_of_product (hp : ProductFormula) {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (ht : t ≠ 1 / 2) :
    rate n t = -(1 / (n : ℝ)) * ∑ k : Fin n, logIntegrand t ((k : ℝ) / n) := by
  rw [rate, hp n hn t ht0 ht1, log_productValue (by omega) (q_norm t) (q_ne_neg_one ht0 ht1 ht)]
  rfl

private lemma problem3_nonmidpoint_of_components (hp : ProductFormula) (hr : (∀ t : ℝ, 0 < t → t < 1 → t ≠ 1 / 2 →
  Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
    ∑ k : Fin n, logIntegrand t ((k : ℝ) / n)) atTop
    (𝓝 (-(∫ x in (0 : ℝ)..1, logIntegrand t x)))))
    (hi : (∀ t : ℝ, 0 < t → t < 1 → t ≠ 1 / 2 →
  -(∫ x in (0 : ℝ)..1, logIntegrand t x) = universal t)) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (ht : t ≠ 1 / 2) :
    Tendsto (fun n : ℕ => rate n t) atTop (𝓝 (universal t)) := by
  have h := hr t ht0 ht1 ht
  rw [hi t ht0 ht1 ht] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (rate_eq_riemann_of_product hp hn ht0 ht1 ht).symm

private lemma midpoint_log_norm_product (m : ℕ) :
    Real.log ‖productValue (2 * m + 1) (-1)‖ = Real.log (midpointAmplitude m) := by
  rw [product_odd_amplitude, norm_mul, norm_pow]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (midpointAmplitude_pos m)]

private lemma midpoint_rate_of_product (hp : ProductFormula) {m : ℕ} (hm : m ≠ 0) :
    rate (2 * m + 1) (1 / 2) =
      1 - Real.log 2 / (2 * m + 1 : ℝ) - midpointLogRatio m / (2 * m + 1 : ℝ) := by
  have hl := log_midpointRatio hm
  unfold midpointRatio at hl
  rw [Real.log_div (midpointAmplitude_pos m).ne' (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_exp] at hl
  unfold rate
  rw [hp _ (by omega) _ (by norm_num) (by norm_num), q_midpoint, midpoint_log_norm_product]
  push_cast
  rw [show Real.log (midpointAmplitude m) = midpointLogRatio m + Real.log 2 - (2 * m + 1 : ℝ) by linarith]
  field_simp
  ring

private lemma midpoint_reciprocal_tendsto :
    Tendsto (fun m : ℕ => (1 : ℝ) / (2 * m + 1 : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun m : ℕ => 2 * m + 1) atTop atTop :=
    tendsto_atTop_mono (fun m => by change m ≤ 2 * m + 1; omega) tendsto_id
  have hr : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  simpa [Function.comp_def, Nat.cast_add, Nat.cast_mul] using hr.comp h

private lemma midpointLogRatio_tendsto : Tendsto midpointLogRatio atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have ht := midpoint_reciprocal_tendsto.const_mul 2
  simp only [mul_zero] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall (fun m => abs_nonneg (midpointLogRatio m))) ?_ ht
  filter_upwards [eventually_ge_atTop 1] with m hm
  simpa [div_eq_mul_inv] using midpointLogRatio_abs_le hm

private lemma midpoint_rate_tendsto_of_product (hp : ProductFormula) :
    Tendsto (fun m : ℕ => rate (2 * m + 1) (1 / 2)) atTop (𝓝 1) := by
  have hlog2 := midpoint_reciprocal_tendsto.const_mul (Real.log 2)
  have hL := midpointLogRatio_tendsto.mul midpoint_reciprocal_tendsto
  have ht := ((tendsto_const_nhds (x := (1 : ℝ))).sub hlog2).sub hL
  simp only [mul_zero, sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [midpoint_rate_of_product hp (by omega : m ≠ 0)]
  simp [div_eq_mul_inv]

theorem result3 : claim3 := by
  constructor
  · intro t ht0 ht1 ht
    exact problem3_nonmidpoint_of_components product_formula logRiemann_limit logIntegral_evaluation ht0 ht1 ht
  · exact midpoint_rate_tendsto_of_product product_formula

#print axioms result3
end CycleGeodesic
