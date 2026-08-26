/- GID: D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliSecondOrder
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/SymmetricBernoulliSecondOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Symmetric Bernoulli evidence has quadratic leading terms and quartic remainders. -/

import D5.S3.TotalVariation.HellingerDivergence

/- Library-search audit trail (2026-08-25):
   * Repository searches for symmetric Bernoulli weak-signal laws and the three
     second-order expansions found no exact declaration. The canonical frozen
     `hellingerSq`, `bhattacharyya`, and `klDivergence` primitives are reused.
   * Pinned Mathlib exact hit `Real.abs_log_sub_add_sum_range_le` supplies a
     local logarithm remainder estimate. `Real.log_sqrt`, `Real.sqrt_sq_eq_abs`,
     and the asymptotics `IsBigO.of_bound` API supply the remaining bridges.
   * No new divergence or probability-law primitive is introduced. The two
     source mass functions are constructed directly on `Bool`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder

open Filter Asymptotics
open D5.S3.Divergence.ClassicalDPI
open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Hellinger

noncomputable section

/-- The symmetric Bernoulli law with positive bias `delta`. -/
def positiveBiasLaw (delta : Real) : Bool -> Real :=
  fun b => if b then 1 / 2 + delta else 1 / 2 - delta

/-- The symmetric Bernoulli law with negative bias `delta`. -/
def negativeBiasLaw (delta : Real) : Bool -> Real :=
  fun b => if b then 1 / 2 - delta else 1 / 2 + delta

private theorem bias_laws_probability_data {delta : Real} (hdelta : |delta| < 1 / 2) :
    ((forall b, 0 <= positiveBiasLaw delta b) /\
      ∑ b, positiveBiasLaw delta b = 1) /\
    ((forall b, 0 <= negativeBiasLaw delta b) /\
      ∑ b, negativeBiasLaw delta b = 1) := by
  have hlower : 0 <= 1 / 2 - delta := by
    rw [abs_lt] at hdelta
    linarith
  have hupper : 0 <= 1 / 2 + delta := by
    rw [abs_lt] at hdelta
    linarith
  constructor <;> constructor
  · intro b
    cases b <;> simp only [positiveBiasLaw, Bool.false_eq_true, ↓reduceIte] <;>
      linarith
  · norm_num [positiveBiasLaw, Fintype.sum_bool]
  · intro b
    cases b <;> simp only [negativeBiasLaw, Bool.false_eq_true, ↓reduceIte] <;>
      linarith
  · norm_num [negativeBiasLaw, Fintype.sum_bool]

private theorem affinity_closed_form {delta : Real} (hdelta : |delta| < 1 / 2) :
    bhattacharyya (positiveBiasLaw delta) (negativeBiasLaw delta) =
      Real.sqrt (1 - 4 * delta ^ 2) := by
  have hplus : 0 <= 1 / 2 + delta := by
    rw [abs_lt] at hdelta
    linarith
  have hminus : 0 <= 1 / 2 - delta := by
    rw [abs_lt] at hdelta
    linarith
  have hproduct : 0 <= (1 / 2 + delta) * (1 / 2 - delta) := by
    exact mul_nonneg hplus hminus
  have hradicand : 0 <= 1 - 4 * delta ^ 2 := by
    nlinarith [sq_nonneg (|delta|), sq_abs delta]
  rw [bhattacharyya]
  simp only [positiveBiasLaw, negativeBiasLaw, Fintype.sum_bool, Bool.false_eq_true,
    ↓reduceIte]
  have hsame :
      (1 / 2 - delta) * (1 / 2 + delta) =
        (1 / 2 + delta) * (1 / 2 - delta) := by ring
  rw [hsame]
  have hsquare :
      (2 * Real.sqrt ((1 / 2 + delta) * (1 / 2 - delta))) ^ 2 =
        (Real.sqrt (1 - 4 * delta ^ 2)) ^ 2 := by
    calc
      (2 * Real.sqrt ((1 / 2 + delta) * (1 / 2 - delta))) ^ 2 =
          4 * Real.sqrt ((1 / 2 + delta) * (1 / 2 - delta)) ^ 2 := by ring
      _ = 4 * ((1 / 2 + delta) * (1 / 2 - delta)) := by
        rw [Real.sq_sqrt hproduct]
      _ = 1 - 4 * delta ^ 2 := by ring
      _ = (Real.sqrt (1 - 4 * delta ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt hradicand]
  have hleft : 0 <= 2 * Real.sqrt ((1 / 2 + delta) * (1 / 2 - delta)) := by positivity
  have hright : 0 <= Real.sqrt (1 - 4 * delta ^ 2) := Real.sqrt_nonneg _
  nlinarith

private theorem hellinger_closed_form {delta : Real} (hdelta : |delta| < 1 / 2) :
    hellingerSq (positiveBiasLaw delta) (negativeBiasLaw delta) =
      2 * (1 - Real.sqrt (1 - 4 * delta ^ 2)) := by
  obtain ⟨hpositive, hnegative⟩ := bias_laws_probability_data hdelta
  rw [hellinger_sq_eq_two_sub _ _ hpositive hnegative, affinity_closed_form hdelta]

private theorem kl_closed_form {delta : Real} (hdelta : |delta| < 1 / 2) :
    klDivergence (positiveBiasLaw delta) (negativeBiasLaw delta) =
      2 * delta * Real.log ((1 + 2 * delta) / (1 - 2 * delta)) := by
  rw [abs_lt] at hdelta
  have hplus : 0 < 1 / 2 + delta := by linarith
  have hminus : 0 < 1 / 2 - delta := by linarith
  rw [klDivergence]
  simp only [positiveBiasLaw, negativeBiasLaw, Fintype.sum_bool, Bool.false_eq_true,
    ↓reduceIte]
  have hreciprocal :
      (1 / 2 - delta) / (1 / 2 + delta) =
        ((1 / 2 + delta) / (1 / 2 - delta))⁻¹ := by
    field_simp [hplus.ne', hminus.ne']
  rw [hreciprocal, Real.log_inv]
  have hratio :
      (1 / 2 + delta) / (1 / 2 - delta) =
        (1 + 2 * delta) / (1 - 2 * delta) := by
    field_simp [hminus.ne']
  rw [hratio]
  ring

private theorem hellinger_remainder_bigO :
    (fun delta : Real =>
      hellingerSq (positiveBiasLaw delta) (negativeBiasLaw delta) - 4 * delta ^ 2)
      =O[nhds 0] (fun delta : Real => delta ^ 4) := by
  apply Asymptotics.IsBigO.of_bound 16
  filter_upwards [Metric.ball_mem_nhds (0 : Real) (by norm_num : (0 : Real) < 1 / 2)]
    with delta hdelta
  have hdelta : |delta| < 1 / 2 := by
    simpa [Metric.mem_ball, Real.dist_eq] using hdelta
  have hradicand : 0 <= 1 - 4 * delta ^ 2 := by
    have hproduct := mul_pos (sub_pos.mpr hdelta)
      (by nlinarith [abs_nonneg delta] : 0 < 1 / 2 + |delta|)
    nlinarith [sq_abs delta]
  have hsquare : Real.sqrt (1 - 4 * delta ^ 2) ^ 2 = 1 - 4 * delta ^ 2 :=
    Real.sq_sqrt hradicand
  have hdenominator : 0 < 1 + Real.sqrt (1 - 4 * delta ^ 2) := by positivity
  rw [hellinger_closed_form hdelta]
  have hremainder :
      2 * (1 - Real.sqrt (1 - 4 * delta ^ 2)) - 4 * delta ^ 2 =
        16 * delta ^ 4 / (1 + Real.sqrt (1 - 4 * delta ^ 2)) ^ 2 := by
    field_simp [hdenominator.ne']
    nlinarith
  rw [hremainder, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_mul]
  rw [abs_of_nonneg (by norm_num : (0 : Real) <= 16),
    abs_of_nonneg (by positivity : 0 <= delta ^ 4),
    abs_of_nonneg (sq_nonneg (1 + Real.sqrt (1 - 4 * delta ^ 2)))]
  have hdenominator_sq : 1 <= (1 + Real.sqrt (1 - 4 * delta ^ 2)) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (1 - 4 * delta ^ 2)]
  calc
    16 * delta ^ 4 / (1 + Real.sqrt (1 - 4 * delta ^ 2)) ^ 2 <=
        16 * delta ^ 4 := by
      exact div_le_self (mul_nonneg (by norm_num) (by positivity)) hdenominator_sq
    _ = 16 * delta ^ 4 := rfl

private theorem affinity_log_remainder_bigO :
    (fun delta : Real =>
      -Real.log (bhattacharyya (positiveBiasLaw delta) (negativeBiasLaw delta)) -
        2 * delta ^ 2)
      =O[nhds 0] (fun delta : Real => delta ^ 4) := by
  apply Asymptotics.IsBigO.of_bound 16
  filter_upwards [Metric.ball_mem_nhds (0 : Real) (by norm_num : (0 : Real) < 1 / 4)]
    with delta hdelta
  have hdelta : |delta| < 1 / 4 := by
    simpa [Metric.mem_ball, Real.dist_eq] using hdelta
  have hhalf : |delta| < 1 / 2 := hdelta.trans (by norm_num)
  have ht_nonneg : 0 <= 4 * delta ^ 2 := by positivity
  have ht_abs : |4 * delta ^ 2| = 4 * delta ^ 2 := abs_of_nonneg ht_nonneg
  have hsquare_lt : delta ^ 2 < (1 / 4 : Real) ^ 2 := by
    have hproduct := mul_pos (sub_pos.mpr hdelta)
      (by nlinarith [abs_nonneg delta] : 0 < 1 / 4 + |delta|)
    nlinarith [sq_abs delta]
  have ht_lt : |4 * delta ^ 2| < 1 := by
    rw [ht_abs]
    nlinarith
  have hlog := Real.abs_log_sub_add_sum_range_le ht_lt 1
  norm_num [Finset.sum_range_succ] at hlog
  have hdenominator : 1 / 2 <= 1 - |4 * delta ^ 2| := by
    rw [ht_abs]
    nlinarith
  rw [affinity_closed_form hhalf, Real.log_sqrt (by nlinarith)]
  have hremainder :
      -(Real.log (1 - 4 * delta ^ 2) / 2) - 2 * delta ^ 2 =
        -(4 * delta ^ 2 + Real.log (1 - 4 * delta ^ 2)) / 2 := by ring
  rw [hremainder, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_neg]
  norm_num
  calc
    |4 * delta ^ 2 + Real.log (1 - 4 * delta ^ 2)| / 2 <=
        (|4 * delta ^ 2| ^ 2 / (1 - |4 * delta ^ 2|)) / 2 := by
      exact div_le_div_of_nonneg_right (by simpa only [ht_abs] using hlog) (by norm_num)
    _ <= |4 * delta ^ 2| ^ 2 := by
      apply div_le_iff₀ (by norm_num : (0 : Real) < 2) |>.2
      exact (div_le_iff₀ (by linarith : 0 < 1 - |4 * delta ^ 2|)).2 (by nlinarith)
    _ = 16 * delta ^ 4 := by
      rw [ht_abs]
      ring
    _ = 16 * |delta| ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= delta ^ 4)]

private theorem kl_remainder_bigO :
    (fun delta : Real =>
      klDivergence (positiveBiasLaw delta) (negativeBiasLaw delta) - 8 * delta ^ 2)
      =O[nhds 0] (fun delta : Real => delta ^ 4) := by
  apply Asymptotics.IsBigO.of_bound 64
  filter_upwards [Metric.ball_mem_nhds (0 : Real) (by norm_num : (0 : Real) < 1 / 4)]
    with delta hdelta
  have hdelta : |delta| < 1 / 4 := by
    simpa [Metric.mem_ball, Real.dist_eq] using hdelta
  let x : Real := 2 * delta
  have hx : |x| < 1 := by
    dsimp [x]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    linarith
  have hnegx : |-x| < 1 := by simpa using hx
  have hminus := Real.abs_log_sub_add_sum_range_le hx 2
  have hplus := Real.abs_log_sub_add_sum_range_le hnegx 2
  norm_num [Finset.sum_range_succ] at hminus hplus
  have hdenominator : 1 / 2 <= 1 - |x| := by
    dsimp [x] at hx ⊢
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)] at hx ⊢
    linarith
  have hlog_difference :
      |Real.log (1 + x) - Real.log (1 - x) - 2 * x| <= 4 * |x| ^ 3 := by
    have hidentity :
        Real.log (1 + x) - Real.log (1 - x) - 2 * x =
          (-x + x ^ 2 / 2 + Real.log (1 + x)) -
            (x + x ^ 2 / 2 + Real.log (1 - x)) := by ring
    rw [hidentity]
    calc
      |(-x + x ^ 2 / 2 + Real.log (1 + x)) -
          (x + x ^ 2 / 2 + Real.log (1 - x))| <=
          |-x + x ^ 2 / 2 + Real.log (1 + x)| +
            |x + x ^ 2 / 2 + Real.log (1 - x)| := abs_sub _ _
      _ <= |x| ^ 3 / (1 - |x|) + |x| ^ 3 / (1 - |x|) := by
        exact add_le_add (by simpa using hplus) (by simpa using hminus)
      _ <= 4 * |x| ^ 3 := by
        have hden_pos : 0 < 1 - |x| := by linarith
        have hone : |x| ^ 3 / (1 - |x|) <= 2 * |x| ^ 3 := by
          apply (div_le_iff₀ hden_pos).2
          nlinarith [pow_nonneg (abs_nonneg x) 3]
        linarith
  have hplus_pos : 0 < 1 + x := by linarith [neg_lt_of_abs_lt hx]
  have hminus_pos : 0 < 1 - x := by linarith [lt_of_abs_lt hx]
  rw [kl_closed_form (hdelta.trans (by norm_num))]
  have hratio :
      Real.log ((1 + 2 * delta) / (1 - 2 * delta)) =
        Real.log (1 + x) - Real.log (1 - x) := by
    dsimp [x]
    exact Real.log_div hplus_pos.ne' hminus_pos.ne'
  rw [hratio]
  have hremainder :
      2 * delta * (Real.log (1 + x) - Real.log (1 - x)) - 8 * delta ^ 2 =
        x * (Real.log (1 + x) - Real.log (1 - x) - 2 * x) := by
    dsimp [x]
    ring
  rw [hremainder, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  calc
    |x| * |Real.log (1 + x) - Real.log (1 - x) - 2 * x| <=
        |x| * (4 * |x| ^ 3) := by gcongr
    _ = 64 * |delta ^ 4| := by
      dsimp [x]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2), abs_pow]
      ring

/-- For the symmetric Bernoulli pair with biases `delta` and `-delta`,
squared Hellinger distance, negative log-affinity, and KL divergence have
quadratic leading terms `4`, `2`, and `8`, respectively, with quartic
remainders as `delta` tends to zero. -/
theorem symmetric_bernoulli_second_order :
    (fun delta : Real =>
      hellingerSq (positiveBiasLaw delta) (negativeBiasLaw delta) - 4 * delta ^ 2)
        =O[nhds 0] (fun delta : Real => delta ^ 4) /\
    (fun delta : Real =>
      -Real.log (bhattacharyya (positiveBiasLaw delta) (negativeBiasLaw delta)) -
        2 * delta ^ 2)
        =O[nhds 0] (fun delta : Real => delta ^ 4) /\
    (fun delta : Real =>
      klDivergence (positiveBiasLaw delta) (negativeBiasLaw delta) - 8 * delta ^ 2)
        =O[nhds 0] (fun delta : Real => delta ^ 4) := by
  exact ⟨hellinger_remainder_bigO, affinity_log_remainder_bigO, kl_remainder_bigO⟩

#print axioms symmetric_bernoulli_second_order

end

end D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder
