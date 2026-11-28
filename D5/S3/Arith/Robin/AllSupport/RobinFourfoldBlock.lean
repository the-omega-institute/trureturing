/- GID: D5/S3/Arith/Robin/AllSupport/RobinFourfoldBlock
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/AllSupport/RobinFourfoldBlock
   mirror-E: none(waiver:robin-fourfold-block)
   anchors: []
   utility: none
   digest: A fourfold prime-reciprocal band inequality characterizes the Riemann hypothesis. -/

import D5.S3.Arith.Robin.ActualRobinClockCovariance
import D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
import D5.S3.Weil.Mertens.RobinWeightedTailConverse
import D5.S3.Weil.Mertens.IntegratedExplicit.RobinActualWeightedBound
import Mathlib.NumberTheory.AbelSummation
import Batteries.Tactic.OpenPrivate

/-! The Robin tail as a sum over fourfold prime-reciprocal bands. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators Interval Topology

namespace D5.S3.Arith.Robin.AllSupport.RobinFourfoldBlock

open D5.S3.Arith.Robin.ActualRobinClockCovariance
  (activationDensity)
open D5.S3.Weil.Mertens.RobinWeightedTailConverse
  (rh_of_eventually_normalized_weighted_tail_lower)
open D5.S3.Weil.Mertens.WeightedTailTransport
  (weightedTail)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
  (firstLiMass)
open D5.S3.Arith.Robin.CompleteMertensPeak
  (psiErrorKernel)
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (Jpsi S)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (G actual_G_control)
open D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace
  (firstLiMass_lt_twentieth)
open private Jpsi_signed_limit S_limit A_limit from D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope

/-! The concrete Robin clock used below. -/

abbrev D := D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.D

abbrev g := D5.S3.Arith.Robin.ActualRobinClockCovariance.g

abbrev w (t : ℝ) : ℝ := activationDensity t

def Jθ (x : ℝ) : ℝ :=
  ∫ t in Ioi x, (Chebyshev.theta t - t) * w t

def B4 (x : ℝ) : ℝ := Jθ x - Jθ (4 * x)

def scale (n : ℝ) (j : ℕ) : ℝ := (4 : ℝ) ^ j * n

def F (t : ℝ) : ℝ := Real.log (Real.log t) - 1 / Real.log t

def primeReciprocal (x y : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, 1 / (p : ℝ)

lemma scale_zero (n : ℝ) : scale n 0 = n := by
  simp [scale]

lemma scale_succ (n : ℝ) (j : ℕ) : scale n (j + 1) = 4 * scale n j := by
  simp [scale, pow_succ]
  ring

lemma g_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt g (-w t) t := by
  exact D5.S3.Arith.Robin.ActualRobinClockCovariance.g_has_deriv_at ht

lemma F_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt F (t * w t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlt : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hloglog :=
    (Real.hasDerivAt_log hlt).comp t (Real.hasDerivAt_log ht0)
  have hinv := (hasDerivAt_const t (1 : ℝ)).div
    (Real.hasDerivAt_log ht0) hlt
  have h := hloglog.sub hinv
  exact h.congr_deriv (by
    simp only [w, activationDensity, one_mul, zero_mul, zero_sub]
    field_simp [ht0, hlt]
    ring)

private lemma weight_continuous {a b : ℝ} (ha : 1 < a) :
    ContinuousOn w (Icc a b) := by
  have hzero (t : ℝ) (ht : t ∈ Icc a b) : t ≠ 0 :=
    (zero_lt_one.trans (ha.trans_le ht.1)).ne'
  have hl : ContinuousOn Real.log (Icc a b) := continuousOn_id.log hzero
  unfold w activationDensity
  exact (hl.add continuousOn_const).div ((continuousOn_id.pow 2).mul (hl.pow 2))
    (fun t ht => mul_ne_zero (pow_ne_zero 2 (hzero t ht))
      (pow_ne_zero 2 (Real.log_pos (ha.trans_le ht.1)).ne'))

private lemma theta_integrable {a : ℝ} (ha : 2 ≤ a) :
    IntegrableOn (fun t => (Chebyshev.theta t - t) * w t) (Ioi a) :=
  (D5.S3.Arith.Robin.ThetaTailRobinWitness.theta_tail_mertens_robin a ha).1

private lemma theta_tail_sub {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    Jθ a - Jθ b = ∫ t in a..b, (Chebyshev.theta t - t) * w t :=
  intervalIntegral.integral_Ioi_sub_Ioi (theta_integrable ha) hab

/-- Finite Abel summation with the right-closed prime band. -/
private lemma theta_abel {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, Chebyshev.theta t * w t) =
      Chebyshev.theta a * g a - Chebyshev.theta b * g b + primeReciprocal a b := by
  classical
  let c : ℕ → ℝ := fun p => if p.Prime then Real.log p else 0
  have hc (t : ℝ) : (∑ p ∈ Finset.Icc 0 ⌊t⌋₊, c p) = Chebyshev.theta t := by
    simp only [c, ← Finset.sum_filter, Chebyshev.theta_eq_sum_Icc]
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt g (-w t) t :=
    g_hasDerivAt (ha.trans_le ht.1)
  have hi : IntegrableOn (deriv g) (Icc a b) :=
    (weight_continuous ha).neg.integrableOn_Icc.congr_fun
      (fun t ht => (hderiv t ht).deriv.symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul c (by linarith : 0 ≤ a) hab
    (fun t ht => (hderiv t ht).differentiableAt) hi
  simp_rw [hc] at habel
  rw [← intervalIntegral.integral_of_le hab] at habel
  have hs : (∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g p * c p) =
      primeReciprocal a b := by
    unfold primeReciprocal
    simp only [c, mul_ite, mul_zero, ← Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    unfold g D5.S3.Arith.Robin.ActualRobinClockCovariance.g
    field_simp [(Real.log_pos hp1).ne', (show (p : ℝ) ≠ 0 by linarith)]
  have hint : (∫ t in a..b, deriv g t * Chebyshev.theta t) =
      -(∫ t in a..b, Chebyshev.theta t * w t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    dsimp only
    rw [(hderiv t ht).deriv]
    ring
  rw [hs, hint] at habel
  linear_combination -habel

/-- The explicit block uses exactly the primes in (x, 4x]. -/
theorem finite_robin_block_identity {x : ℝ} (hx : 2 ≤ x) :
    B4 x = Chebyshev.theta x * g x - Chebyshev.theta (4 * x) * g (4 * x) +
      primeReciprocal x (4 * x) - (F (4 * x) - F x) := by
  have hle : x ≤ 4 * x := by linarith
  have hx1 : 1 < x := by linarith
  have ht : IntervalIntegrable (fun t => t * w t) volume x (4 * x) :=
    (continuousOn_id.mul (weight_continuous hx1)).intervalIntegrable_of_Icc hle
  have hf : (∫ t in x..(4 * x), t * w t) = F (4 * x) - F x := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ ht
    intro t h
    rw [uIcc_of_le hle] at h
    exact F_hasDerivAt (hx1.trans_le h.1)
  have herr : IntervalIntegrable (fun t => (Chebyshev.theta t - t) * w t)
      volume x (4 * x) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr
      ((theta_integrable hx).mono_set Ioc_subset_Ioi_self)
  have hθ : IntervalIntegrable (fun t => Chebyshev.theta t * w t) volume x (4 * x) := by
    have he : (fun t => Chebyshev.theta t * w t) =
        (fun t => (Chebyshev.theta t - t) * w t + t * w t) := by
      funext t
      ring
    rw [he]
    exact herr.add ht
  have hsplit : (∫ t in x..(4 * x), (Chebyshev.theta t - t) * w t) =
      (∫ t in x..(4 * x), Chebyshev.theta t * w t) -
        (∫ t in x..(4 * x), t * w t) := by
    rw [← intervalIntegral.integral_sub hθ ht]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  change Jθ x - Jθ (4 * x) = _
  rw [theta_tail_sub hx hle, hsplit, theta_abel hx1 hle, hf]

/-! Finite fourfold telescoping, with no analytic hypotheses. -/

lemma telescope_B4 {D J B : ℝ → ℝ} {n : ℝ} (k : ℕ)
    (hB : ∀ x : ℝ, B x = J x - J (4 * x)) :
    D n * J n =
      (∑ j ∈ Finset.range k, D n * B (scale n j)) +
        D n * J (scale n k) := by
  induction k with
  | zero => simp [scale]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, hB (scale n k), scale_succ]
      ring

/-!
  Geometric tail transfer.  The only limiting input is the vanishing
  remainder along the fourfold orbit.  Every finite partial sum is bounded
  below by the finite geometric sum, whose exact value is retained in the
  proof instead of invoking an asymptotic estimate.
-/

theorem geometric_tail_transfer {D J B : ℝ → ℝ} {n : ℝ}
    (hB : ∀ x : ℝ, B x = J x - J (4 * x))
    (hD : ∀ j : ℕ, 0 < D (scale n j))
    (hblock : ∀ j : ℕ,
      -(11 / 10 : ℝ) ≤ D (scale n j) * B (scale n j))
    (hratio : ∀ j : ℕ,
      D n / D (scale n j) ≤ (1 / 2 : ℝ) ^ j)
    (hrem : Tendsto (fun j : ℕ => D n * J (scale n j))
      atTop (𝓝 0)) :
    D n * J n ≥ -(11 / 5 : ℝ) := by
  have hterm : ∀ j : ℕ,
      -(11 / 10 : ℝ) * (1 / 2 : ℝ) ^ j ≤
        D n * B (scale n j) := by
    intro j
    have hratio_nonneg : 0 ≤ D n / D (scale n j) := by
      exact div_nonneg (by simpa only [scale_zero] using (hD 0).le) (hD j).le
    have hscaled :=
      mul_le_mul_of_nonneg_left (hblock j) hratio_nonneg
    have hrewrite :
        (D n / D (scale n j)) * (D (scale n j) * B (scale n j)) =
          D n * B (scale n j) := by
      field_simp [ne_of_gt (hD j)] <;> ring
    have hscaled' :
        -(11 / 10 : ℝ) * (D n / D (scale n j)) ≤
          D n * B (scale n j) := by
      rw [hrewrite, mul_comm (D n / D (scale n j))] at hscaled
      exact hscaled
    have hratio' := mul_le_mul_of_nonpos_left (hratio j)
      (by norm_num : -(11 / 10 : ℝ) ≤ 0)
    exact hratio'.trans hscaled'
  have hgeom : ∀ k : ℕ,
      (∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j) =
        2 - 2 * (1 / 2 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        ring
  have hpartial : ∀ k : ℕ,
      -(11 / 5 : ℝ) ≤
        ∑ j ∈ Finset.range k, D n * B (scale n j) := by
    intro k
    have hs := Finset.sum_le_sum (s := Finset.range k) (fun j _ => hterm j)
    have hneg : -(11 / 5 : ℝ) ≤
        ∑ j ∈ Finset.range k,
          -(11 / 10 : ℝ) * (1 / 2 : ℝ) ^ j := by
      rw [← Finset.mul_sum, hgeom k]
      have hpow : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
      nlinarith
    exact hneg.trans hs
  by_contra hnot
  have hlt : D n * J n < -(11 / 5 : ℝ) := lt_of_not_ge hnot
  let ε : ℝ := (-(11 / 5 : ℝ) - D n * J n) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hev : ∀ᶠ j : ℕ in atTop,
      -ε < D n * J (scale n j) := by
    have hnhd : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hrem.eventually hnhd] with j hj
    exact hj.1
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  have htail := hK K le_rfl
  have htelescope := telescope_B4 (D := D) (n := n) K hB
  have hp := hpartial K
  dsimp only [ε] at htail
  linarith only [htail, htelescope, hp, hlt]

private lemma D_pos {x : ℝ} (hx : 1 < x) : 0 < D x :=
  mul_pos (Real.sqrt_pos.mpr (zero_lt_one.trans hx)) (Real.log_pos hx)

private lemma D_four {x : ℝ} (hx : 0 < x) :
    D (4 * x) = 2 * Real.sqrt x * (Real.log 4 + Real.log x) := by
  change Real.sqrt (4 * x) * Real.log (4 * x) = _
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hx.ne']
  norm_num

private lemma D_four_ge {x : ℝ} (hx : 1 < x) : 2 * D x ≤ D (4 * x) := by
  rw [D_four (zero_lt_one.trans hx)]
  change 2 * (Real.sqrt x * Real.log x) ≤ _
  nlinarith only [mul_nonneg (Real.sqrt_nonneg x)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))]

theorem fourfold_ratio_limit :
    Tendsto (fun x : ℝ => D x / D (4 * x)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlog : Tendsto (fun x : ℝ => Real.log 4 / Real.log x)
      atTop (𝓝 0) :=
    (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
  have hscalar : Tendsto (fun z : ℝ => 1 / (2 * (1 + z)))
      (𝓝 0) (𝓝 (1 / 2 : ℝ)) := by
    have hc : ContinuousAt (fun z : ℝ => 2 * (1 + z)) 0 := by fun_prop
    have h : ContinuousAt (fun z : ℝ => (1 : ℝ) / (2 * (1 + z))) 0 :=
      continuousAt_const.div hc (by norm_num)
    simpa only [ContinuousAt, add_zero, mul_one] using h
  have hcomp := hscalar.comp hlog
  apply hcomp.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hlx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  rw [D_four hx0]
  dsimp [Function.comp_def, D, D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.D]
  field_simp [hlx, hsx]
  ring

private lemma scale_ge {n : ℝ} (hn : 0 ≤ n) (j : ℕ) : n ≤ scale n j := by
  change n ≤ (4 : ℝ) ^ j * n
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4) (n := j)) hn

private lemma D_scale_ge {n : ℝ} (hn : 1 < n) (j : ℕ) :
    (2 : ℝ) ^ j * D n ≤ D (scale n j) := by
  induction j with
  | zero => simp [scale]
  | succ j ih =>
      rw [pow_succ, scale_succ]
      calc
        _ = 2 * ((2 : ℝ) ^ j * D n) := by ring
        _ ≤ 2 * D (scale n j) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ _ := D_four_ge (hn.trans_le (scale_ge (by linarith) j))

private lemma D_scale_ratio {n : ℝ} (hn : 1 < n) (j : ℕ) :
    D n / D (scale n j) ≤ (1 / 2 : ℝ) ^ j := by
  have hj := D_pos (hn.trans_le (scale_ge (by linarith) j))
  apply (div_le_iff₀ hj).2
  have h := mul_le_mul_of_nonneg_left (D_scale_ge hn j)
    (show 0 ≤ (1 / 2 : ℝ) ^ j by positivity)
  have he : (1 / 2 : ℝ) ^ j * ((2 : ℝ) ^ j * D n) = D n := by
    rw [← mul_assoc, ← mul_pow]
    norm_num
  simpa only [he] using h

/-- The integer hypothesis supplies the geometric estimate on every fourfold orbit. -/
theorem integer_tail_lower
    (h : ∀ᶠ n : ℕ in atTop, -(11 / 10 : ℝ) ≤ D (n : ℝ) * B4 (n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, -(11 / 5 : ℝ) ≤ D (n : ℝ) * Jθ (n : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop (max N 2)] with n hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hscale : Tendsto (scale (n : ℝ)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).atTop_mul_const
      (zero_lt_one.trans hn1)
  have htail : Tendsto Jθ atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero (f := fun t => (Chebyshev.theta t - t) * w t) tendsto_id
  refine geometric_tail_transfer (D := D) (J := Jθ) (B := B4) (n := (n : ℝ))
    (fun _ => rfl) (fun j => D_pos (hn1.trans_le (scale_ge (by positivity) j)))
    (fun j => ?_) (D_scale_ratio hn1) ?_
  · have hj : n ≤ 4 ^ j * n := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right n (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 4) (n := j))
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, scale] using
      hN (4 ^ j * n) ((le_max_left _ _).trans (hn.trans hj))
  · simpa only [mul_zero, Function.comp_def] using
      (htail.comp hscale).const_mul (D (n : ℝ))

private lemma w_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ w t := by
  unfold w activationDensity
  have := Real.log_pos ht
  positivity

/-- On a unit interval above x, the one-sided bound only needs theta's nonnegativity. -/
private lemma adjacent_tail_lower {x y : ℝ} (hx : 4 ≤ x)
    (hlx : 1 ≤ Real.log x) (hxy : x ≤ y) (hy : y ≤ x + 1) :
    -(2 / Real.sqrt x) ≤ D x * (Jθ x - Jθ y) := by
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := by linarith
  let c : ℝ := 2 / (x * Real.log x)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hint : IntervalIntegrable (fun t => (Chebyshev.theta t - t) * w t) volume x y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).mpr
      ((theta_integrable (by linarith : 2 ≤ x)).mono_set Ioc_subset_Ioi_self)
  have hbound (t : ℝ) (ht : t ∈ Icc x y) :
      -c ≤ (Chebyshev.theta t - t) * w t := by
    have ht0 : 0 < t := hx0.trans_le ht.1
    have hlt := hlx.trans (Real.log_le_log hx0 ht.1)
    have hlt0 : 0 < Real.log t := by linarith
    have he : t * w t = (1 + 1 / Real.log t) / (t * Real.log t) := by
      unfold w activationDensity
      field_simp [ht0.ne', hlt0.ne']
    have hden : x * Real.log x ≤ t * Real.log t :=
      mul_le_mul ht.1 (Real.log_le_log hx0 ht.1) hlx0.le ht0.le
    have hltinv : 1 / Real.log t ≤ 1 := (div_le_iff₀ hlt0).2 (by linarith)
    have htw : t * w t ≤ c := calc
      _ = (1 + 1 / Real.log t) / (t * Real.log t) := he
      _ ≤ 2 / (t * Real.log t) :=
        div_le_div_of_nonneg_right (by linarith) (mul_nonneg ht0.le hlt0.le)
      _ ≤ c := div_le_div_of_nonneg_left (by norm_num) (mul_pos hx0 hlx0) hden
    rw [sub_mul]
    linarith only [htw, mul_nonneg (Chebyshev.theta_nonneg t)
      (w_nonneg (by linarith [ht.1] : 1 < t))]
  have hIntegral := intervalIntegral.integral_mono_on hxy intervalIntegrable_const hint hbound
  rw [intervalIntegral.integral_const, smul_eq_mul, ← theta_tail_sub (by linarith : 2 ≤ x) hxy]
    at hIntegral
  have hdiff : -c ≤ Jθ x - Jθ y := by
    nlinarith only [hIntegral, mul_nonneg hc (show 0 ≤ 1 - (y - x) by linarith)]
  have hD := D_pos (show 1 < x by linarith)
  have hDc : D x * c = 2 / Real.sqrt x := by
    dsimp [D, D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.D, c]
    have hs0 := Real.sqrt_pos.mpr hx0
    field_simp [hx0.ne', hlx0.ne', hs0.ne']
    nlinarith only [Real.sq_sqrt hx0.le]
  have hscaled := mul_le_mul_of_nonneg_left hdiff hD.le
  rwa [mul_neg, hDc] at hscaled

/-- Transfer the integer lower bound to the reals with any positive allowance. -/
theorem eventual_real_lower {ε : ℝ} (hε : 0 < ε)
    (h : ∀ᶠ n : ℕ in atTop, -(11 / 5 : ℝ) ≤ D (n : ℝ) * Jθ (n : ℝ)) :
    ∀ᶠ x : ℝ in atTop, -(11 / 5 : ℝ) - ε ≤ D x * Jθ x := by
  have he : Tendsto (fun x : ℝ => 2 / Real.sqrt x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop (max (N : ℝ) 4),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    he.eventually (Iio_mem_nhds hε)] with x hx hlog hsmall
  let y : ℝ := (⌈x⌉₊ : ℝ)
  have hx4 : 4 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hxy : x ≤ y := Nat.le_ceil x
  have hy : y ≤ x + 1 := (Nat.ceil_lt_add_one hx0.le).le
  have hNy : N ≤ ⌈x⌉₊ := by
    have hreal : (N : ℝ) ≤ y := ((le_max_left _ _).trans hx).trans hxy
    change (N : ℝ) ≤ (⌈x⌉₊ : ℝ) at hreal
    exact_mod_cast hreal
  have hJy : -(11 / 5 : ℝ) ≤ D y * Jθ y := hN _ hNy
  have hDx := D_pos (show 1 < x by linarith)
  have hDy := D_pos (show 1 < y by linarith)
  have hmon : D x ≤ D y :=
    mul_le_mul (Real.sqrt_le_sqrt hxy) (Real.log_le_log hx0 hxy)
      (by linarith) (Real.sqrt_nonneg y)
  have hr := div_nonneg hDx.le hDy.le
  have hr1 := (div_le_one hDy).2 hmon
  have hscaled := mul_le_mul_of_nonneg_left hJy hr
  have he : D x / D y * (D y * Jθ y) = D x * Jθ y := by
    field_simp [hDy.ne'] <;> ring
  rw [he] at hscaled
  have hlocal := adjacent_tail_lower hx4 hlog hxy hy
  rw [mul_sub] at hlocal
  change 2 / Real.sqrt x < ε at hsmall
  linarith only [hscaled, hlocal, hr1, hsmall]

/-! The RH numerical block estimate, once the normalized theta envelope is in
  hand.  This is the exact algebra used with `r = D x / D (4*x)`. -/

theorem rh_block_lower_at {x : ℝ} (hDx : 0 ≤ D x)
    (hD4 : 0 < D (4 * x))
    (hJx : |D x * Jθ x + 2| ≤ (1 / 20 : ℝ))
    (hJ4 : |D (4 * x) * Jθ (4 * x) + 2| ≤ (1 / 20 : ℝ)) :
    D x * B4 x ≥
      -2 * (1 - D x / D (4 * x)) -
        (1 + D x / D (4 * x)) / 20 := by
  let r : ℝ := D x / D (4 * x)
  have hr : 0 ≤ r := (div_nonneg hDx (hD4.le))
  have hxlow : -(2 : ℝ) - 1 / 20 ≤ D x * Jθ x := by
    have := (abs_le.mp hJx).1
    linarith
  have h4up : D (4 * x) * Jθ (4 * x) ≤ -(2 : ℝ) + 1 / 20 := by
    have := (abs_le.mp hJ4).2
    linarith
  have htransport : D x * Jθ (4 * x) =
      r * (D (4 * x) * Jθ (4 * x)) := by
    dsimp [r]
    field_simp [ne_of_gt hD4]
  have h4scaled := mul_le_mul_of_nonneg_left h4up hr
  rw [B4, mul_sub, htransport]
  dsimp [r] at h4scaled ⊢
  nlinarith

private theorem psi_weightedTail_eq_Jpsi (x : ℝ) :
    weightedTail psiErrorKernel x =
      D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.Jpsi x := by
  unfold weightedTail D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.Jpsi
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.weighted_eq t

private theorem theta_psi_split {x : ℝ} (hx : 2 ≤ x) :
    D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.Jpsi x -
        D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.S x = Jθ x := by
  have ht := D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.tails hx
  rw [D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.Jpsi,
    D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.S, Jθ,
    ← integral_sub ht.1 ht.2.1]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  ring

private theorem theta_center_limit (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ => D x * Jθ x + 2 + G (Real.log x)) atTop (𝓝 0) := by
  have h := (Jpsi_signed_limit hRH).sub ((S_limit hRH).sub_const 2)
  rw [sub_self, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [← theta_psi_split hx]
  ring

private theorem theta_center_bound (hRH : RiemannHypothesis) :
    ∀ᶠ x : ℝ in atTop, |D x * Jθ x + 2| ≤ (1 / 20 : ℝ) := by
  let δ := (1 / 20 - firstLiMass) / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith [firstLiMass_lt_twentieth]
  have he := (Metric.tendsto_nhds.mp (theta_center_limit hRH)) δ hδ
  have hg := Real.tendsto_log_atTop.eventually ((actual_G_control hRH).1 δ hδ)
  filter_upwards [he, hg] with x hx hxg
  rw [Real.dist_eq, sub_zero] at hx
  have h := abs_sub (D x * Jθ x + 2 + G (Real.log x)) (G (Real.log x))
  rw [add_sub_cancel_right] at h
  dsimp [δ] at hx hxg
  linarith [firstLiMass_lt_twentieth]

private theorem block_lower_of_rh (hRH : RiemannHypothesis) :
    ∀ᶠ x : ℝ in atTop, -(11 / 10 : ℝ) ≤ D x * B4 x := by
  have hθ := theta_center_bound hRH
  have h4 := (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 4)).mpr
    (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop)
  have hr := fourfold_ratio_limit.eventually
    (Ioi_mem_nhds (by norm_num : (49 / 100 : ℝ) < 1 / 2))
  filter_upwards [hθ, h4.eventually hθ, eventually_ge_atTop (2 : ℝ), hr] with x hx h4x hx2 hratio
  change |D (4 * x) * Jθ (4 * x) + 2| ≤ (1 / 20 : ℝ) at h4x
  change (49 / 100 : ℝ) < D x / D (4 * x) at hratio
  have h := rh_block_lower_at (D_pos (by linarith only [hx2])).le
    (D_pos (by linarith only [hx2])) hx h4x
  linarith only [h, hratio]

/-- An eventual lower bound in the fourfold prime reciprocal band is equivalent
to RH. The count and the boundary terms use only ordinary primes. -/
theorem rh_iff_eventual_integer_fourfold_robin_block :
    RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop, -(11 / 10 : ℝ) ≤
      D (n : ℝ) * (Chebyshev.theta (n : ℝ) * g (n : ℝ) -
        Chebyshev.theta (4 * (n : ℝ)) * g (4 * (n : ℝ)) +
        primeReciprocal (n : ℝ) (4 * (n : ℝ)) - (F (4 * (n : ℝ)) - F (n : ℝ))) := by
  have hformula : ∀ᶠ n : ℕ in atTop, B4 (n : ℝ) =
      Chebyshev.theta (n : ℝ) * g (n : ℝ) -
        Chebyshev.theta (4 * (n : ℝ)) * g (4 * (n : ℝ)) +
        primeReciprocal (n : ℝ) (4 * (n : ℝ)) - (F (4 * (n : ℝ)) - F (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact finite_robin_block_identity (by exact_mod_cast hn)
  constructor
  · intro hRH
    have hb := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (block_lower_of_rh hRH)
    filter_upwards [hb, hformula] with n hn hf
    simpa only [hf] using hn
  · intro h
    have hb : ∀ᶠ n : ℕ in atTop, -(11 / 10 : ℝ) ≤ D (n : ℝ) * B4 (n : ℝ) := by
      filter_upwards [h, hformula] with n hn hf
      simpa only [hf] using hn
    have htail := eventual_real_lower (by norm_num : (0 : ℝ) < 1 / 50)
      (integer_tail_lower hb)
    have hS : Tendsto (fun x : ℝ => D x * S x) atTop (𝓝 2) := by
      simpa only [mul_sub, sub_add_cancel, zero_add] using
        D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.S_sub_A_limit.add A_limit
    apply rh_of_eventually_normalized_weighted_tail_lower
    refine ⟨111 / 50, ?_⟩
    filter_upwards [htail, hS.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 2)),
      eventually_ge_atTop (2 : ℝ)] with x hx hs hx2
    change 0 < D x * S x at hs
    rw [psi_weightedTail_eq_Jpsi]
    have he := theta_psi_split hx2
    nlinarith only [hx, hs, congrArg (D x * ·) he]


#print axioms rh_iff_eventual_integer_fourfold_robin_block

end D5.S3.Arith.Robin.AllSupport.RobinFourfoldBlock
