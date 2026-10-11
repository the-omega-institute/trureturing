/- GID: D5/S3/Factorization/Combinatorics/MixedPrimeHistoryAsymptotics
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/MixedPrimeHistoryAsymptotics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Subcritical geometric control of the actual weighted mixed prime histories. -/

import D5.S3.Factorization.Combinatorics.MixedPrimeHistoryGenerating
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Complex.LocallyUniformLimit

set_option autoImplicit false

namespace D5.S3.Factorization.Combinatorics.MixedPrimeHistoryAsymptotics

open D5.S3.Factorization.Combinatorics.MixedPrimeHistoryCount
open D5.S3.Factorization.Combinatorics.MixedPrimeHistoryGenerating
open scoped BigOperators NNReal ENNReal

/-- The prime-supported geometric series, on its disk of convergence. -/
noncomputable def primeSeries {𝕜 : Type*} [NormedField 𝕜] (z : 𝕜) : 𝕜 :=
  ∑' q : ℕ, if q.Prime then z ^ q else 0

/-- The ordinary generating series of all endpoint weights. -/
noncomputable def generating (t : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (weightedCount t n : ℂ) * z ^ n

/-- The numerator obtained from the multiplicative last letters. -/
noncomputable def numerator (t : ℝ) (z : ℂ) : ℂ :=
  z + (t : ℂ) * ∑' q : ℕ, if q.Prime then generating t (z ^ q) else 0

private theorem length_lt_endpoint (n : ℕ) (hn : 0 < n)
    (w : List PrimeLetter) (hw : endpoint w = n) : w.length < n := by
  by_cases he : w = []
  · simp [he, hn]
  · have hb := sharp_length_bound w he
    rw [hw] at hb
    omega

private theorem weighted_length_sum (t : ℝ) (n N : ℕ) (hn : 0 < n) (hN : n ≤ N) :
    weightedCount t n = ∑ k ∈ Finset.range N, (lengthCount k n : ℝ) * t ^ k := by
  classical
  let s := (reachable_finite n hn).2.toFinset
  have hmaps : ∀ w ∈ s, w.length ∈ Finset.range N := by
    intro w hw
    have he : endpoint w = n := (reachable_finite n hn).2.mem_toFinset.mp hw
    exact Finset.mem_range.mpr ((length_lt_endpoint n hn w he).trans_le hN)
  rw [weightedCount, dif_pos hn, ← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro k hk
  have hs : (↑(s.filter (fun w => w.length = k)) : Set (List PrimeLetter)) =
      {w | endpoint w = n ∧ w.length = k} := by
    ext w
    simp [s, historyFibre]
  have hc : (s.filter (fun w => w.length = k)).card = lengthCount k n := by
    change _ = ({w : List PrimeLetter | endpoint w = n ∧ w.length = k} : Set _).ncard
    rw [← hs, Set.ncard_coe_finset]
  calc
    ∑ w ∈ s with w.length = k, t ^ w.length =
        ∑ w ∈ s with w.length = k, t ^ k := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [(Finset.mem_filter.mp hw).2]
    _ = _ := by simp [hc]

private theorem weighted_nonneg (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ weightedCount t n := by
  classical
  unfold weightedCount
  split_ifs
  · exact Finset.sum_nonneg (fun _ _ => pow_nonneg ht _)
  · exact le_rfl

private theorem weighted_zero (t : ℝ) : weightedCount t 0 = 0 := by
  simp [weightedCount]

private theorem weighted_one (t : ℝ) : weightedCount t 1 = 1 := by
  rw [weighted_length_sum t 1 1 (by omega) le_rfl]
  have h := mixed_coefficient 1 0 1 (by omega) le_rfl
  simpa [mixedPolynomial] using congrArg (fun x : ℕ => (x : ℝ)) h.symm

private theorem weighted_recurrence (t : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    weightedCount t n = t *
      ((∑ q ∈ (Finset.range n).filter Nat.Prime, weightedCount t (n - q)) +
       (∑ q ∈ n.primeFactors, weightedCount t (n / q))) := by
  classical
  have hz : lengthCount 0 n = 0 := by
    have h := mixed_coefficient n 0 n (by omega) le_rfl
    simpa [mixedPolynomial, Polynomial.coeff_X, show 1 ≠ n by omega] using h.symm
  have hl (k : ℕ) : lengthCount (k + 1) n =
      (∑ q ∈ (Finset.range n).filter Nat.Prime, lengthCount k (n - q)) +
      (∑ q ∈ n.primeFactors, lengthCount k (n / q)) := by
    simpa using length_recurrence (k + 1) n (by omega) hn
  rw [weighted_length_sum t n n (by omega) le_rfl]
  conv_lhs => rw [show Finset.range n = Finset.range ((n - 1) + 1) by congr 1; omega,
    Finset.sum_range_succ']
  simp only [hz, Nat.cast_zero, zero_mul, add_zero]
  simp_rw [hl,
    Nat.cast_add, Nat.cast_sum, add_mul, Finset.sum_mul, pow_succ]
  rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_comm (s := Finset.range (n - 1))]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro q hq
    have hqn := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
    have hqp := (Finset.mem_filter.mp hq).2.pos
    rw [weighted_length_sum t (n - q) (n - 1) (by omega) (by omega), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  · apply Finset.sum_congr rfl
    intro q hq
    have hpos := Nat.div_pos (Nat.le_of_mem_primeFactors hq)
      (Nat.pos_of_mem_primeFactors hq)
    have hlt := Nat.div_lt_self (show 0 < n by omega)
      (Nat.prime_of_mem_primeFactors hq).one_lt
    rw [weighted_length_sum t (n / q) (n - 1) hpos (by omega), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring

private theorem prime_summable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun q : ℕ => if q.Prime then r ^ q else 0) := by
  apply Summable.of_nonneg_of_le
    (fun q => by split_ifs <;> positivity)
    (fun q => show (if q.Prime then r ^ q else 0) ≤ r ^ q by
      split_ifs
      · exact le_rfl
      · exact pow_nonneg hr q)
    (summable_geometric_of_lt_one hr hr1)

/-- Below the prime-series threshold, one constant controls every actual endpoint. -/
theorem subcritical_bound (t r : ℝ) (ht : 0 < t) (hr : 0 < r) (hr1 : r < 1)
    (hsub : t * primeSeries r < 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, weightedCount t n * r ^ n ≤ B := by
  classical
  have hs0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hs1 : Real.sqrt r < 1 := by
    simpa using Real.sqrt_lt_sqrt hr.le hr1
  have hlim : Filter.Tendsto
      (fun n : ℕ => t * (primeSeries r + (n : ℝ) * (Real.sqrt r) ^ n))
      Filter.atTop (nhds (t * primeSeries r)) := by
    simpa using (tendsto_self_mul_const_pow_of_lt_one hs0 hs1).const_add
      (primeSeries r) |>.const_mul t
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_order.mp hlim).2 1 hsub)
  let M := max N 2
  let B := 1 + ∑ k ∈ Finset.range M, weightedCount t k * r ^ k
  have hB : 0 < B := by
    have h := Finset.sum_nonneg (s := Finset.range M)
      (fun k _ => mul_nonneg (weighted_nonneg t ht.le k) (pow_nonneg hr.le k))
    dsimp [B]
    linarith
  refine ⟨B, hB, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n < M
    · have h := Finset.single_le_sum
        (fun k (_ : k ∈ Finset.range M) =>
          mul_nonneg (weighted_nonneg t ht.le k) (pow_nonneg hr.le k))
        (Finset.mem_range.mpr hsmall)
      dsimp [B]
      linarith
    · have hn : 2 ≤ n := le_trans (le_max_right N 2) (Nat.le_of_not_gt hsmall)
      have ha :
          (∑ q ∈ (Finset.range n).filter Nat.Prime,
            weightedCount t (n - q) * r ^ n) ≤ B * primeSeries r := by
        calc
          _ ≤ ∑ q ∈ (Finset.range n).filter Nat.Prime, B * r ^ q := by
            apply Finset.sum_le_sum
            intro q hq
            have hqlt := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
            have hqpos := (Finset.mem_filter.mp hq).2.pos
            calc
              weightedCount t (n - q) * r ^ n =
                  (weightedCount t (n - q) * r ^ (n - q)) * r ^ q := by
                    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hqlt.le]
              _ ≤ B * r ^ q := mul_le_mul_of_nonneg_right
                (ih (n - q) (by omega)) (pow_nonneg hr.le q)
          _ = B * (∑ q ∈ (Finset.range n).filter Nat.Prime, r ^ q) :=
            (Finset.mul_sum _ _ _).symm
          _ ≤ B * primeSeries r := by
            apply mul_le_mul_of_nonneg_left _ hB.le
            rw [Finset.sum_filter]
            exact Summable.sum_le_tsum (Finset.range n)
              (fun q _ => by split_ifs <;> positivity) (prime_summable r hr.le hr1)
      have hm : (∑ q ∈ n.primeFactors, weightedCount t (n / q) * r ^ n) ≤
          B * ((n : ℝ) * (Real.sqrt r) ^ n) := by
        have hcard : n.primeFactors.card ≤ n := by
          calc
            n.primeFactors.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card (by
              intro q hq
              exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_primeFactors hq,
                Nat.le_of_mem_primeFactors hq⟩)
            _ = n := by simp
        calc
          _ ≤ ∑ _q ∈ n.primeFactors, B * (Real.sqrt r) ^ n := by
            apply Finset.sum_le_sum
            intro q hq
            have hq2 := (Nat.prime_of_mem_primeFactors hq).two_le
            have hqn : n / q < n := Nat.div_lt_self (by omega) (by omega)
            have hhalf : n / q ≤ n / 2 := Nat.div_le_div_left hq2 (by omega)
            have hexp : n ≤ 2 * (n - n / q) := by omega
            have hp : r ^ (n - n / q) ≤ (Real.sqrt r) ^ n := by
              calc
                _ = (Real.sqrt r) ^ (2 * (n - n / q)) := by
                  rw [pow_mul, Real.sq_sqrt hr.le]
                _ ≤ _ := pow_le_pow_of_le_one hs0 hs1.le hexp
            calc
              weightedCount t (n / q) * r ^ n =
                  (weightedCount t (n / q) * r ^ (n / q)) * r ^ (n - n / q) := by
                    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hqn.le]
              _ ≤ B * r ^ (n - n / q) := mul_le_mul_of_nonneg_right
                (ih _ hqn) (pow_nonneg hr.le _)
              _ ≤ B * (Real.sqrt r) ^ n := mul_le_mul_of_nonneg_left hp hB.le
          _ = B * ((n.primeFactors.card : ℝ) * (Real.sqrt r) ^ n) := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            ring
          _ ≤ B * ((n : ℝ) * (Real.sqrt r) ^ n) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg hs0 _)) hB.le
      calc
        weightedCount t n * r ^ n = t *
            ((∑ q ∈ (Finset.range n).filter Nat.Prime,
                weightedCount t (n - q) * r ^ n) +
             (∑ q ∈ n.primeFactors, weightedCount t (n / q) * r ^ n)) := by
              rw [weighted_recurrence t n hn]
              simp only [← Finset.sum_mul]
              ring
        _ ≤ t * (B * primeSeries r + B * ((n : ℝ) * (Real.sqrt r) ^ n)) :=
          mul_le_mul_of_nonneg_left (add_le_add ha hm) ht.le
        _ = B * (t * (primeSeries r + (n : ℝ) * (Real.sqrt r) ^ n)) := by ring
        _ ≤ B * 1 := mul_le_mul_of_nonneg_left
          (hN n (le_trans (le_max_left N 2) (Nat.le_of_not_gt hsmall))).le hB.le
        _ = B := mul_one B

private theorem norm_term_bound (t r B : ℝ) (ht : 0 ≤ t) (hr : 0 < r)
    (hB : ∀ n : ℕ, weightedCount t n * r ^ n ≤ B) (z : ℂ) (n : ℕ) :
    ‖(weightedCount t n : ℂ) * z ^ n‖ ≤ B * (‖z‖ / r) ^ n := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (weighted_nonneg t ht n)]
  calc
    weightedCount t n * ‖z‖ ^ n =
        (weightedCount t n * r ^ n) * (‖z‖ / r) ^ n := by
          rw [mul_assoc, ← mul_pow, mul_div_cancel₀ _ hr.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right (hB n) (pow_nonneg (by positivity) _)

private theorem norm_summable (t r B : ℝ) (ht : 0 ≤ t) (hr : 0 < r)
    (hB : ∀ n : ℕ, weightedCount t n * r ^ n ≤ B) (z : ℂ) (hz : ‖z‖ < r) :
    Summable (fun n : ℕ => ‖(weightedCount t n : ℂ) * z ^ n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_term_bound t r B ht hr hB z)
    ((summable_geometric_of_lt_one (by positivity : 0 ≤ ‖z‖ / r)
      ((div_lt_one hr).mpr hz)).mul_left B)

private theorem generating_analytic_of_bound (t r B : ℝ) (ht : 0 ≤ t) (hr : 0 < r)
    (hB : ∀ n : ℕ, weightedCount t n * r ^ n ≤ B) :
    AnalyticOnNhd ℂ (generating t) (Metric.ball 0 r) := by
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => (weightedCount t n : ℂ))
  let rnn : ℝ≥0 := ⟨r, hr.le⟩
  have hp : (rnn : ℝ≥0∞) ≤ p.radius :=
    p.le_radius_of_bound B (r := rnn) (fun n => by
      change ‖p n‖ * r ^ n ≤ B
      simpa [p, FormalMultilinearSeries.ofScalars_norm, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (weighted_nonneg t ht n)] using hB n)
  intro z hz
  have hzr : (‖z‖₊ : ℝ≥0∞) < (rnn : ℝ≥0∞) := by
    exact_mod_cast (show ‖z‖ < r by simpa using hz)
  have ha := p.analyticOnNhd z (by simpa [enorm_eq_nnnorm] using hzr.trans_le hp)
  change AnalyticAt ℂ (FormalMultilinearSeries.ofScalarsSum
    (fun n => (weightedCount t n : ℂ))) z at ha
  change AnalyticAt ℂ (fun x : ℂ => ∑' n : ℕ, (weightedCount t n : ℂ) * x ^ n) z
  simpa only [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul] using ha

private theorem norm_sum_le (t r B : ℝ) (ht : 0 ≤ t) (hr : 0 < r)
    (hB : ∀ n : ℕ, weightedCount t n * r ^ n ≤ B) (z : ℂ) (hz : ‖z‖ < r) :
    (∑' n : ℕ, ‖(weightedCount t n : ℂ) * z ^ n‖) ≤ B * ‖z‖ / (r - ‖z‖) := by
  have hs := norm_summable t r B ht hr hB z hz
  have hu0 : 0 ≤ ‖z‖ / r := by positivity
  have hu1 : ‖z‖ / r < 1 := (div_lt_one hr).mpr hz
  have htail := (summable_geometric_of_lt_one hu0 hu1).mul_left B
  have hshift := htail.comp_injective (add_left_injective (1 : ℕ))
  rw [← hs.sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_one, weighted_zero, Complex.ofReal_zero, zero_mul,
    norm_zero, zero_add]
  calc
    (∑' n : ℕ, ‖(weightedCount t (n + 1) : ℂ) * z ^ (n + 1)‖) ≤
        ∑' n : ℕ, B * (‖z‖ / r) ^ (n + 1) :=
      (hs.comp_injective (add_left_injective (1 : ℕ))).tsum_le_tsum
        (fun n => norm_term_bound t r B ht hr hB z (n + 1)) hshift
    _ = B * ‖z‖ / (r - ‖z‖) := by
      simp_rw [pow_succ, ← mul_assoc]
      rw [tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one hu0 hu1]
      field_simp

private theorem generating_norm_le (t r B : ℝ) (ht : 0 ≤ t) (hr : 0 < r)
    (hB : ∀ n : ℕ, weightedCount t n * r ^ n ≤ B) (z : ℂ) (hz : ‖z‖ < r) :
    ‖generating t z‖ ≤ B * ‖z‖ / (r - ‖z‖) :=
  (norm_tsum_le_tsum_norm (norm_summable t r B ht hr hB z hz)).trans
    (norm_sum_le t r B ht hr hB z hz)

private theorem prime_power_norm (r a : ℝ) (hr1 : r < 1) (ha : 0 ≤ a) (har : a ^ 2 < r)
    (q : ℕ) (hq : q.Prime) (z : ℂ) (hz : ‖z‖ ≤ a) :
    ‖z ^ q‖ ≤ a ^ q ∧ a ^ q ≤ a ^ 2 ∧ ‖z ^ q‖ < r := by
  have ha1 : a ≤ 1 := by nlinarith
  have h1 : ‖z ^ q‖ ≤ a ^ q := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hz _
  have h2 := pow_le_pow_of_le_one ha ha1 hq.two_le
  exact ⟨h1, h2, lt_of_le_of_lt (h1.trans h2) har⟩

private theorem composition_norm_bound (t r B a : ℝ) (ht : 0 ≤ t) (hr : 0 < r)
    (hr1 : r < 1) (hB0 : 0 ≤ B) (hB : ∀ n : ℕ, weightedCount t n * r ^ n ≤ B)
    (ha : 0 ≤ a) (har : a ^ 2 < r) (q : ℕ) (hq : q.Prime)
    (z : ℂ) (hz : ‖z‖ ≤ a) :
    ‖generating t (z ^ q)‖ ≤ B * a ^ q / (r - a ^ 2) := by
  have hp := prime_power_norm r a hr1 ha har q hq z hz
  exact (generating_norm_le t r B ht hr hB _ hp.2.2).trans
    (div_le_div₀ (mul_nonneg hB0 (pow_nonneg ha _))
      (mul_le_mul_of_nonneg_left hp.1 hB0) (sub_pos.mpr har) (by linarith [hp.1, hp.2.1]))

private theorem numerator_analytic_of_bound (t r B : ℝ) (ht : 0 ≤ t) (hr : 0 < r)
    (hr1 : r < 1) (hB0 : 0 ≤ B) (hB : ∀ n : ℕ, weightedCount t n * r ^ n ≤ B) :
    AnalyticOnNhd ℂ (numerator t) (Metric.ball 0 (Real.sqrt r)) := by
  classical
  intro z hz
  have hz' : ‖z‖ < Real.sqrt r := by simpa using hz
  obtain ⟨a, hza, har⟩ := exists_between hz'
  have ha : 0 ≤ a := (norm_nonneg z).trans hza.le
  have ha1 : a < 1 := har.trans (by simpa using Real.sqrt_lt_sqrt hr.le hr1)
  have ha2 : a ^ 2 < r := by
    nlinarith [Real.sq_sqrt hr.le, Real.sqrt_nonneg r]
  have hs : Summable (fun q : ℕ => B * a ^ q / (r - a ^ 2)) :=
    ((summable_geometric_of_lt_one ha ha1).mul_left B).div_const _
  have hd : DifferentiableOn ℂ
      (fun w : ℂ => ∑' q : ℕ, if q.Prime then generating t (w ^ q) else 0)
      (Metric.ball 0 a) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hs ?_ Metric.isOpen_ball ?_
    · intro q w hw
      by_cases hq : q.Prime
      · simp only [if_pos hq]
        have hp := (prime_power_norm r a hr1 ha ha2 q hq w
          (by simpa using (Metric.mem_ball.mp hw).le)).2.2
        exact ((generating_analytic_of_bound t r B ht hr hB _ (by simpa using hp)).differentiableAt.comp
          w (differentiableAt_id.pow q)).differentiableWithinAt
      · simp only [if_neg hq]
        exact differentiableWithinAt_const _
    · intro q w hw
      by_cases hq : q.Prime
      · simpa only [if_pos hq] using composition_norm_bound t r B a ht hr hr1 hB0 hB
          ha ha2 q hq w (by simpa using (Metric.mem_ball.mp hw).le)
      · simp only [if_neg hq, norm_zero]
        positivity
  exact analyticAt_id.add (analyticAt_const.mul
    (hd.analyticOnNhd Metric.isOpen_ball z (by simpa using hza)))

/-- One endpoint bound also controls every prime composition on each smaller closed disk. -/
theorem subcritical_analytic_control (t r : ℝ) (ht : 0 < t) (hr : 0 < r) (hr1 : r < 1)
    (hsub : t * primeSeries r < 1) :
    ∃ B : ℝ, 0 < B ∧ (∀ n : ℕ, weightedCount t n * r ^ n ≤ B) ∧
      AnalyticOnNhd ℂ (generating t) (Metric.ball 0 r) ∧
      (∀ a : ℝ, 0 ≤ a → a ^ 2 < r → ∀ q : ℕ, q.Prime →
        ∀ z : ℂ, ‖z‖ ≤ a → ‖generating t (z ^ q)‖ ≤ B * a ^ q / (r - a ^ 2)) ∧
      AnalyticOnNhd ℂ (numerator t) (Metric.ball 0 (Real.sqrt r)) := by
  obtain ⟨B, hB0, hB⟩ := subcritical_bound t r ht hr hr1 hsub
  exact ⟨B, hB0, hB, generating_analytic_of_bound t r B ht.le hr hB,
    fun a ha har q hq z hz => composition_norm_bound t r B a ht.le hr hr1 hB0.le hB ha har q hq z hz,
    numerator_analytic_of_bound t r B ht.le hr hr1 hB0.le hB⟩

end D5.S3.Factorization.Combinatorics.MixedPrimeHistoryAsymptotics
