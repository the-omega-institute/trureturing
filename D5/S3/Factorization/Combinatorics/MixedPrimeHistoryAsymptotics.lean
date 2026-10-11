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
import Mathlib.Analysis.Normed.Ring.InfiniteSum

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

set_option maxHeartbeats 800000 in
-- Reindexing both the complex series and its norm series elaborates the same infinite sum twice.
private theorem multiplicative_series (t r B : ℝ) (ht : 0 ≤ t) (hr : 0 < r)
    (hr1 : r < 1) (hB0 : 0 ≤ B) (hB : ∀ n : ℕ, weightedCount t n * r ^ n ≤ B)
    (z : ℂ) (hz : ‖z‖ < r) :
    HasSum (fun n : ℕ => ∑ q ∈ n.primeFactors, (weightedCount t (n / q) : ℂ) * z ^ n)
      (∑' q : ℕ, if q.Prime then generating t (z ^ q) else 0) := by
  classical
  let D (q n : ℕ) : ℂ :=
    if q.Prime ∧ q ∣ n then (weightedCount t (n / q) : ℂ) * z ^ n else 0
  have hz1 : ‖z‖ < 1 := hz.trans hr1
  have hz2 : ‖z‖ ^ 2 < r := by nlinarith [norm_nonneg z]
  have rows (q : ℕ) : Summable (fun n => ‖D q n‖) ∧
      HasSum (D q) (if q.Prime then generating t (z ^ q) else 0) ∧
      (∑' n : ℕ, ‖D q n‖) ≤ B * ‖z‖ ^ q / (r - ‖z‖ ^ 2) := by
    by_cases hq : q.Prime
    · have hi : Function.Injective (fun m : ℕ => q * m) :=
        fun _ _ h => Nat.eq_of_mul_eq_mul_left hq.pos h
      have hzero (n : ℕ) (hn : n ∉ Set.range (fun m : ℕ => q * m)) : D q n = 0 := by
        have hd : ¬ q ∣ n := by
          rintro ⟨m, rfl⟩
          exact hn ⟨m, rfl⟩
        simp [D, hd]
      have hcomp (m : ℕ) : D q (q * m) =
          (weightedCount t m : ℂ) * (z ^ q) ^ m := by
        simp [D, hq, Nat.mul_div_cancel_left _ hq.pos, pow_mul]
      have hp := prime_power_norm r ‖z‖ hr1 (norm_nonneg z) hz2 q hq z le_rfl
      have hs := norm_summable t r B ht hr hB (z ^ q) hp.2.2
      have hn : HasSum (fun n => ‖D q n‖)
          (∑' m : ℕ, ‖(weightedCount t m : ℂ) * (z ^ q) ^ m‖) :=
        (hi.hasSum_iff (fun n hn => by rw [hzero n hn, norm_zero])).mp (by
          simpa only [Function.comp_def, hcomp] using hs.hasSum)
      refine ⟨hn.summable, ?_, ?_⟩
      · rw [if_pos hq]
        apply (hi.hasSum_iff hzero).mp
        simpa only [Function.comp_def, hcomp, generating] using hs.of_norm.hasSum
      · rw [hn.tsum_eq]
        exact (norm_sum_le t r B ht hr hB _ hp.2.2).trans
          (div_le_div₀ (mul_nonneg hB0 (pow_nonneg (norm_nonneg z) _))
            (mul_le_mul_of_nonneg_left hp.1 hB0) (sub_pos.mpr hz2)
            (by linarith [hp.1, hp.2.1]))
    · simp only [D, hq, false_and, if_false, norm_zero, tsum_zero]
      exact ⟨summable_zero, hasSum_zero, by positivity⟩
  have hd : Summable (fun p : ℕ × ℕ => ‖D p.1 p.2‖) := by
    apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
    refine ⟨fun q => (rows q).1, ?_⟩
    exact Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
      (fun q => (rows q).2.2)
      (((summable_geometric_of_lt_one (norm_nonneg z) hz1).mul_left B).div_const _)
  have hcoeff (n : ℕ) : (∑' q : ℕ, D q n) =
      ∑ q ∈ n.primeFactors, (weightedCount t (n / q) : ℂ) * z ^ n := by
    by_cases hn : n = 0
    · subst n
      simp [D, weighted_zero]
    · rw [tsum_eq_sum (s := n.primeFactors) (fun q hq => by
        have hh : ¬ (q.Prime ∧ q ∣ n) := by
          intro h
          exact hq (Nat.mem_primeFactors.mpr ⟨h.1, h.2, hn⟩)
        simp [D, hh])]
      apply Finset.sum_congr rfl
      intro q hq
      simp [D, Nat.prime_of_mem_primeFactors hq, Nat.dvd_of_mem_primeFactors hq]
  have hval : (∑' n : ℕ, ∑' q : ℕ, D q n) =
      ∑' q : ℕ, if q.Prime then generating t (z ^ q) else 0 :=
    hd.of_norm.tsum_comm.trans (tsum_congr (fun q => (rows q).2.1.tsum_eq))
  have hh := hd.of_norm.prod_symm.prod.hasSum
  change HasSum (fun n : ℕ => ∑' q : ℕ, D q n) (∑' n : ℕ, ∑' q : ℕ, D q n) at hh
  rw [hval] at hh
  simpa only [hcoeff] using hh

private theorem prime_norm_summable (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun q : ℕ => ‖if q.Prime then z ^ q else 0‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (f := fun q => ‖z‖ ^ q)
  · intro q
    split_ifs <;> simp [norm_pow]
  · exact summable_geometric_of_lt_one (norm_nonneg _) hz

private theorem additive_series (t r B : ℝ) (ht : 0 ≤ t) (hr : 0 < r)
    (hr1 : r < 1) (hB : ∀ n : ℕ, weightedCount t n * r ^ n ≤ B)
    (z : ℂ) (hz : ‖z‖ < r) :
    HasSum (fun n : ℕ => ∑ q ∈ (Finset.range n).filter Nat.Prime,
      (weightedCount t (n - q) : ℂ) * z ^ n) (primeSeries z * generating t z) := by
  classical
  have hp := prime_norm_summable z (hz.trans hr1)
  have h := hasSum_sum_range_mul_of_summable_norm hp (norm_summable t r B ht hr hB z hz)
  have hc (n : ℕ) :
      (∑ q ∈ Finset.range (n + 1), (if q.Prime then z ^ q else 0) *
        ((weightedCount t (n - q) : ℂ) * z ^ (n - q))) =
      ∑ q ∈ (Finset.range n).filter Nat.Prime, (weightedCount t (n - q) : ℂ) * z ^ n := by
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, weighted_zero, Complex.ofReal_zero, zero_mul, mul_zero, add_zero]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hp : q.Prime
    · simp only [if_pos hp]
      rw [mul_left_comm, ← pow_add, Nat.add_sub_of_le (Finset.mem_range.mp hq).le]
    · simp [hp]
  simpa only [hc, primeSeries, generating] using h

/-- Absolute convergence permits the actual last-letter recurrence to be summed. -/
theorem subcritical_functional_equation (t r : ℝ) (ht : 0 < t) (hr : 0 < r)
    (hr1 : r < 1) (hsub : t * primeSeries r < 1) (z : ℂ) (hz : ‖z‖ < r) :
    (1 - (t : ℂ) * primeSeries z) * generating t z = numerator t z := by
  classical
  obtain ⟨B, hB0, hB⟩ := subcritical_bound t r ht hr hr1 hsub
  have ha := additive_series t r B ht.le hr hr1 hB z hz
  have hm := multiplicative_series t r B ht.le hr hr1 hB0.le hB z hz
  have hbase : HasSum (fun n : ℕ => if n = 1 then z else 0) z :=
    hasSum_ite_eq 1 z
  have hrec := hbase.add ((ha.add hm).mul_left (t : ℂ))
  have hcoeff (n : ℕ) :
      (if n = 1 then z else 0) + (t : ℂ) *
        ((∑ q ∈ (Finset.range n).filter Nat.Prime, (weightedCount t (n - q) : ℂ) * z ^ n) +
         (∑ q ∈ n.primeFactors, (weightedCount t (n / q) : ℂ) * z ^ n)) =
      (weightedCount t n : ℂ) * z ^ n := by
    by_cases hn0 : n = 0
    · subst n
      simp [weighted_zero]
    by_cases hn1 : n = 1
    · subst n
      simp [weighted_one, Finset.sum_filter, Nat.not_prime_zero]
    · rw [if_neg hn1, zero_add, weighted_recurrence t n (by omega)]
      push_cast
      simp only [← Finset.sum_mul]
      ring
  have hrec' : HasSum (fun n : ℕ => (weightedCount t n : ℂ) * z ^ n)
      (z + (t : ℂ) * (primeSeries z * generating t z +
        ∑' q : ℕ, if q.Prime then generating t (z ^ q) else 0)) := by
    simpa only [hcoeff] using hrec
  have hf := hrec'.tsum_eq
  change generating t z = _ at hf
  unfold numerator
  linear_combination hf

private theorem prime_zero : primeSeries (0 : ℝ) = 0 := by
  calc
    _ = ∑' _q : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro q
      by_cases hq : q.Prime
      · simp [hq, zero_pow hq.ne_zero]
      · simp [hq]
    _ = 0 := tsum_zero

private theorem prime_continuous (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    ContinuousOn (primeSeries (𝕜 := ℝ)) (Set.Icc 0 a) := by
  classical
  apply continuousOn_tsum (u := fun q : ℕ => a ^ q)
  · intro q
    by_cases hq : q.Prime
    · simpa only [if_pos hq] using (continuous_pow q).continuousOn
    · simpa only [if_neg hq] using continuousOn_const (c := (0 : ℝ))
  · exact summable_geometric_of_lt_one ha ha1
  · intro q x hx
    by_cases hq : q.Prime
    · simp only [if_pos hq, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1 q)]
      exact pow_le_pow_left₀ hx.1 hx.2 _
    · simp only [if_neg hq, norm_zero]
      exact pow_nonneg ha _

private theorem prime_strict (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) (hy : y < 1) :
    primeSeries x < primeSeries y := by
  apply Summable.tsum_lt_tsum (i := 2)
  · intro q
    by_cases hq : q.Prime
    · simp only [if_pos hq]
      exact pow_le_pow_left₀ hx hxy.le _
    · simp only [if_neg hq, le_refl]
  · simp only [Nat.prime_two, if_true]
    nlinarith
  · exact prime_summable x hx (hxy.trans hy)
  · exact prime_summable y (hx.trans hxy.le) hy

private theorem prime_crosses (t : ℝ) (ht : 0 < t) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ 1 < t * primeSeries a := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / t)
  have hNt : 1 < t * (N : ℝ) := by
    have h := (div_lt_iff₀ ht).mp hN
    linarith
  obtain ⟨S, hS, hcard⟩ := Nat.infinite_setOfPred_prime.exists_subset_card_eq N
  have hc : ContinuousAt (fun x : ℝ => t * ∑ q ∈ S, x ^ q) 1 := by fun_prop
  have hev : ∀ᶠ x : ℝ in nhds 1, 1 < t * ∑ q ∈ S, x ^ q :=
    (tendsto_order.mp hc.tendsto).1 1 (by simpa [hcard] using hNt)
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨ε, hε0, hε⟩ := exists_between (lt_min hδ (by norm_num : (0 : ℝ) < 1))
  have hεδ : ε < δ := hε.trans_le (min_le_left _ _)
  have hε1 : ε < 1 := hε.trans_le (min_le_right _ _)
  have ha0 : 0 < 1 - ε := by linarith
  have ha1 : 1 - ε < 1 := by linarith
  refine ⟨1 - ε, ha0, ha1, ?_⟩
  have hlarge : 1 < t * ∑ q ∈ S, (1 - ε) ^ q :=
    hnear (by simpa [Real.dist_eq, abs_of_nonneg hε0.le] using hεδ)
  have hsum : (∑ q ∈ S, (1 - ε) ^ q) ≤ primeSeries (1 - ε) := by
    calc
      _ = ∑ q ∈ S, if q.Prime then (1 - ε) ^ q else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [if_pos (show q.Prime from hS hq)]
      _ ≤ _ := Summable.sum_le_tsum S (fun q _ => by split_ifs <;> positivity)
        (prime_summable _ ha0.le ha1)
  exact hlarge.trans_le (mul_le_mul_of_nonneg_left hsum ht.le)

private theorem unique_critical_root (t : ℝ) (ht : 0 < t) :
    ∃! ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ t * primeSeries ρ = 1 := by
  obtain ⟨a, ha0, ha1, hat⟩ := prime_crosses t ht
  have hc := (continuousOn_const (c := t)).mul (prime_continuous a ha0.le ha1)
  obtain ⟨ρ, hρa, hρ⟩ := intermediate_value_Icc ha0.le hc
    (show (1 : ℝ) ∈ Set.Icc (t * primeSeries 0) (t * primeSeries a) by
      rw [prime_zero, mul_zero]
      exact ⟨by norm_num, hat.le⟩)
  change t * primeSeries ρ = 1 at hρ
  have hρ0 : 0 < ρ := by
    have hn : ρ ≠ 0 := by intro h; simp [h, prime_zero] at hρ
    exact lt_of_le_of_ne hρa.1 (Ne.symm hn)
  have hρ1 : ρ < 1 := hρa.2.trans_lt ha1
  refine ⟨ρ, ⟨hρ0, hρ1, hρ⟩, ?_⟩
  intro σ hσ
  apply le_antisymm
  · by_contra h
    have hx := mul_lt_mul_of_pos_left (prime_strict ρ σ hρ0.le (lt_of_not_ge h) hσ.2.1) ht
    rw [hρ, hσ.2.2] at hx
    exact (lt_irrefl _ hx)
  · by_contra h
    have hx := mul_lt_mul_of_pos_left (prime_strict σ ρ hσ.1.le (lt_of_not_ge h) hρ1) ht
    rw [hρ, hσ.2.2] at hx
    exact (lt_irrefl _ hx)

private theorem prime_derivative_positive (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (primeSeries (𝕜 := ℂ)) (d : ℂ) (ρ : ℂ) := by
  classical
  obtain ⟨a, hρa, ha1⟩ := exists_between hρ1
  have ha0 : 0 ≤ a := (hρ0.trans hρa).le
  have hf (q : ℕ) : DifferentiableOn ℂ (fun z : ℂ => if q.Prime then z ^ q else 0)
      (Metric.ball 0 a) := by
    by_cases hq : q.Prime <;> simp only [hq, if_true, if_false] <;> fun_prop
  have hnorm (q : ℕ) (z : ℂ) (hz : z ∈ Metric.ball 0 a) :
      ‖if q.Prime then z ^ q else 0‖ ≤ a ^ q := by
    by_cases hq : q.Prime
    · simp only [if_pos hq, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg z) (by simpa using (Metric.mem_ball.mp hz).le) _
    · simp only [if_neg hq, norm_zero]
      exact pow_nonneg ha0 _
  have hs := Complex.hasSum_deriv_of_summable_norm
    (summable_geometric_of_lt_one ha0 ha1) hf Metric.isOpen_ball hnorm
    (show (ρ : ℂ) ∈ Metric.ball 0 a by simpa [abs_of_pos hρ0] using hρa)
  have hr : HasSum (fun q : ℕ => if q.Prime then (q : ℝ) * ρ ^ (q - 1) else 0)
      (deriv (primeSeries (𝕜 := ℂ)) (ρ : ℂ)).re := by
    have h := Complex.hasSum_re hs
    change HasSum _ (deriv (primeSeries (𝕜 := ℂ)) (ρ : ℂ)).re at h
    apply h.congr_fun
    intro q
    by_cases hq : q.Prime <;> simp [hq, deriv_pow_field, ← Complex.ofReal_pow]
  have hi : (deriv (primeSeries (𝕜 := ℂ)) (ρ : ℂ)).im = 0 := by
    have h := Complex.hasSum_im hs
    have he : (fun q : ℕ => (deriv (fun z : ℂ => if q.Prime then z ^ q else 0) (ρ : ℂ)).im) =
        fun _ => (0 : ℝ) := by
      funext q
      by_cases hq : q.Prime <;> simp [hq, deriv_pow_field, ← Complex.ofReal_pow]
    rw [he] at h
    exact h.unique hasSum_zero
  have hp : 0 < (deriv (primeSeries (𝕜 := ℂ)) (ρ : ℂ)).re := by
    rw [← hr.tsum_eq]
    apply hr.summable.tsum_pos (fun q => by split_ifs <;> positivity) 2
    simp only [Nat.prime_two, if_true]
    positivity
  refine ⟨_, hp, ?_⟩
  have hd := (Complex.differentiableOn_tsum_of_summable_norm
    (summable_geometric_of_lt_one ha0 ha1) hf Metric.isOpen_ball hnorm).differentiableAt
    (Metric.isOpen_ball.mem_nhds (show (ρ : ℂ) ∈ Metric.ball 0 a by
      simpa [abs_of_pos hρ0] using hρa))
  have he : ((deriv (primeSeries (𝕜 := ℂ)) (ρ : ℂ)).re : ℂ) =
      deriv (primeSeries (𝕜 := ℂ)) (ρ : ℂ) := by
    apply Complex.ext <;> simp [hi]
  rw [he]
  exact hd.hasDerivAt

set_option maxHeartbeats 800000 in
-- Nonnegative prime deficits identify two separate complex powers before cancellation.
private theorem critical_zero_unique (t ρ : ℝ) (ht : 0 < t) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hroot : t * primeSeries ρ = 1) (z : ℂ) (hz : ‖z‖ ≤ ρ)
    (hzero : 1 - (t : ℂ) * primeSeries z = 0) : z = (ρ : ℂ) := by
  classical
  have hp := prime_norm_summable z (hz.trans_lt hρ1)
  have hn : ‖primeSeries z‖ ≤ primeSeries ‖z‖ := by
    have h := norm_tsum_le_tsum_norm hp
    simpa only [primeSeries, apply_ite norm, norm_pow, norm_zero] using h
  have hprod : (t : ℂ) * primeSeries z = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm : ‖z‖ = ρ := by
    apply le_antisymm hz
    by_contra hh
    have hl := mul_lt_mul_of_pos_left
      (prime_strict ‖z‖ ρ (norm_nonneg z) (lt_of_not_ge hh) hρ1) ht
    have hb := mul_le_mul_of_nonneg_left hn ht.le
    have he := congrArg norm hprod
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, norm_one] at he
    rw [hroot] at hl
    linarith
  have hreal : (primeSeries z).re = primeSeries ρ := by
    have h := congrArg Complex.re hprod
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.one_re] at h
    nlinarith [hroot]
  let e (q : ℕ) : ℝ := if q.Prime then ρ ^ q - (z ^ q).re else 0
  have he0 (q : ℕ) : 0 ≤ e q := by
    by_cases hq : q.Prime
    · have h := Complex.re_le_norm (z ^ q)
      rw [norm_pow, hnorm] at h
      simpa [e, hq] using sub_nonneg.mpr h
    · simp [e, hq]
  have hs : HasSum e 0 := by
    have h := (prime_summable ρ hρ0.le hρ1).hasSum.sub (Complex.hasSum_re hp.of_norm.hasSum)
    have hc (q : ℕ) :
        (if q.Prime then ρ ^ q else 0) - (if q.Prime then z ^ q else 0).re = e q := by
      by_cases hq : q.Prime <;> simp [e, hq]
    change HasSum _ (primeSeries ρ - (primeSeries z).re) at h
    rw [hreal, sub_self] at h
    exact h.congr_fun (fun q => (hc q).symm)
  have he (q : ℕ) : e q = 0 := by
    apply le_antisymm _ (he0 q)
    have h := hs.summable.le_tsum q (fun j _ => he0 j)
    rwa [hs.tsum_eq] at h
  have hpower (q : ℕ) (hq : q.Prime) : z ^ q = (ρ : ℂ) ^ q := by
    have hre : (z ^ q).re = ρ ^ q := by have h := he q; simp [e, hq] at h; linarith
    have him : (z ^ q).im = 0 := Complex.abs_re_eq_norm.mp (by
      rw [hre, norm_pow, hnorm, abs_of_nonneg (pow_nonneg hρ0.le _)])
    apply Complex.ext <;> simp [hre, him, ← Complex.ofReal_pow]
  have h2 := hpower 2 Nat.prime_two
  have h3 := hpower 3 Nat.prime_three
  have hx : (ρ : ℂ) ^ 2 * z = (ρ : ℂ) ^ 2 * (ρ : ℂ) := by
    calc
      _ = z ^ 2 * z := by rw [h2]
      _ = z ^ 3 := (pow_succ z 2).symm
      _ = _ := h3.trans (pow_succ (ρ : ℂ) 2)
  exact mul_left_cancel₀ (pow_ne_zero 2 (by exact_mod_cast hρ0.ne')) hx

/-- The unique critical radius supports the common endpoint and prime-composition bounds. -/
theorem critical_control (t : ℝ) (ht : 0 < t) :
    ∃ ρ : ℝ, (0 < ρ ∧ ρ < 1 ∧ t * primeSeries ρ = 1) ∧
      (∀ σ : ℝ, 0 < σ → σ < 1 → t * primeSeries σ = 1 → σ = ρ) ∧
      (∀ r : ℝ, 0 < r → r < ρ →
        ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, weightedCount t n * r ^ n ≤ B) ∧
      AnalyticOnNhd ℂ (generating t) (Metric.ball 0 ρ) ∧
      AnalyticOnNhd ℂ (numerator t) (Metric.ball 0 (Real.sqrt ρ)) ∧
      (∀ z : ℂ, ‖z‖ < ρ →
        (1 - (t : ℂ) * primeSeries z) * generating t z = numerator t z) ∧
      (∀ a : ℝ, 0 ≤ a → a ^ 2 < ρ → ∃ r : ℝ, a ^ 2 < r ∧ r < ρ ∧
        ∃ B : ℝ, 0 < B ∧ (∀ n : ℕ, weightedCount t n * r ^ n ≤ B) ∧
          ∀ q : ℕ, q.Prime → ∀ z : ℂ, ‖z‖ ≤ a →
            ‖generating t (z ^ q)‖ ≤ B * a ^ q / (r - a ^ 2)) ∧
      (∃ d : ℝ, 0 < d ∧ HasDerivAt (primeSeries (𝕜 := ℂ)) (d : ℂ) (ρ : ℂ)) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → 1 - (t : ℂ) * primeSeries z = 0 → z = (ρ : ℂ)) := by
  obtain ⟨ρ, hρ, huniq⟩ := unique_critical_root t ht
  have hsub (r : ℝ) (hr : 0 < r) (hrρ : r < ρ) : t * primeSeries r < 1 := by
    rw [← hρ.2.2]
    exact mul_lt_mul_of_pos_left (prime_strict r ρ hr.le hrρ hρ.2.1) ht
  have control (r : ℝ) (hr : 0 < r) (hrρ : r < ρ) :=
    subcritical_analytic_control t r ht hr (hrρ.trans hρ.2.1) (hsub r hr hrρ)
  refine ⟨ρ, hρ, fun σ hσ0 hσ1 hσ => huniq σ ⟨hσ0, hσ1, hσ⟩,
    fun r hr hrρ => subcritical_bound t r ht hr (hrρ.trans hρ.2.1) (hsub r hr hrρ),
    ?_, ?_, ?_, ?_, prime_derivative_positive ρ hρ.1 hρ.2.1,
    critical_zero_unique t ρ ht hρ.1 hρ.2.1 hρ.2.2⟩
  · intro z hz
    obtain ⟨r, hzr, hrρ⟩ := exists_between (show ‖z‖ < ρ by simpa using hz)
    obtain ⟨B, _, _, ha, _⟩ := control r ((norm_nonneg z).trans_lt hzr) hrρ
    exact ha z (by simpa using hzr)
  · intro z hz
    have hz' : ‖z‖ < Real.sqrt ρ := by simpa using hz
    have hzsq : ‖z‖ ^ 2 < ρ := by
      nlinarith [Real.sq_sqrt hρ.1.le, norm_nonneg z, Real.sqrt_nonneg ρ]
    obtain ⟨r, hzr, hrρ⟩ := exists_between hzsq
    obtain ⟨B, _, _, _, _, ha⟩ := control r ((sq_nonneg _).trans_lt hzr) hrρ
    apply ha z
    have h := (Real.lt_sqrt (norm_nonneg z)).mpr hzr
    simpa using h
  · intro z hz
    obtain ⟨r, hzr, hrρ⟩ := exists_between hz
    have hr := (norm_nonneg z).trans_lt hzr
    exact subcritical_functional_equation t r ht hr (hrρ.trans hρ.2.1) (hsub r hr hrρ) z hzr
  · intro a ha haρ
    obtain ⟨r, har, hrρ⟩ := exists_between haρ
    obtain ⟨B, hB0, hB, _, hcomp, _⟩ := control r ((sq_nonneg _).trans_lt har) hrρ
    exact ⟨r, har, hrρ, B, hB0, hB, hcomp a ha har⟩

end D5.S3.Factorization.Combinatorics.MixedPrimeHistoryAsymptotics
