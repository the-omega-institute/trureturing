/- GID: D5/S3/Observer/ProbabilisticClosure/ConditionalClockMomentComparison
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/ConditionalClockMomentComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.SpecificFunctions.Basic]
   utility: none
   digest: Conditional positive clock drift controls adaptive acquisition tails. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SharpChallengeInstrument
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

noncomputable section

open scoped ENNReal BigOperators Classical
open MeasureTheory ProbabilityTheory
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SharpChallengeInstrument

namespace D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison

variable {A Y : Type} [Fintype A] [Fintype Y]

/-- The actual history law for history-dependent source rows and a common adaptive policy.
A world and a request are fixed parameters of the source rows, not of the policy. -/
def historyLaw (κ : ∀ n, Record A Y n → A → PMF Y) (π : Policy A Y) :
    (n : ℕ) → PMF (Record A Y n)
  | 0 => PMF.pure ()
  | n + 1 => (historyLaw κ π n).bind fun h =>
      (π n h).bind fun a => (κ n h a).map fun y => (h, a, y)

/-- The actual additive clock on a complete finite acquired history. -/
def clock (c : ∀ n, Record A Y n → A → Y → ℝ) : (n : ℕ) → Record A Y n → ℝ
  | 0, _ => 0
  | n + 1, h => clock c n h.1 + c n h.1 h.2.1 h.2.2

private theorem history_law_succ (κ : ∀ n, Record A Y n → A → PMF Y)
    (π : Policy A Y) (n : ℕ) (h : Record A Y n) (a : A) (y : Y) :
    historyLaw κ π (n + 1) (h, a, y) =
      historyLaw κ π n h * (π n h a * κ n h a y) := by
  classical
  simp [historyLaw, PMF.bind_apply, PMF.map_apply, tsum_fintype,
    Prod.mk.injEq, ite_and, Finset.sum_ite_irrel, mul_ite]

private theorem pmf_sum_real {Z : Type*} [Fintype Z] (p : PMF Z) :
    ∑ z, (p z).toReal = 1 := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  simpa only [tsum_fintype, ENNReal.toReal_sum (fun z _ => p.apply_ne_top z),
    ENNReal.toReal_one] using h

private theorem exp_neg_chord {C x : ℝ} (hC : 0 < C) (hx0 : 0 ≤ x) (hxC : x ≤ C) :
    Real.exp (-x / C) ≤ 1 - (1 - Real.exp (-1)) / C * x := by
  have ht0 : 0 ≤ x / C := div_nonneg hx0 hC.le
  have ht1 : x / C ≤ 1 := (div_le_one hC).2 hxC
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
    (show 0 ≤ 1 - x / C by linarith) ht0 (show (1 - x / C) + x / C = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_neg_one, Real.exp_zero, mul_one] at h
  convert h using 1 <;> congr 1 <;> ring

/-- The uniform contraction factor at inverse scale C. -/
def rate (μ C : ℝ) : ℝ := 1 - μ / C * (1 - Real.exp (-1))

/-- The positive linear clock threshold. -/
def slope (μ C : ℝ) : ℝ := -(C / 2) * Real.log (rate μ C)

/-- The geometric low-clock tail factor. -/
def tailRate (μ C : ℝ) : ℝ := Real.sqrt (rate μ C)

private theorem row_laplace {Z : Type*} [Fintype Z] (p : PMF Z)
    (c : Z → ℝ) {μ C : ℝ} (hC : 0 < C)
    (hc : ∀ z, 0 ≤ c z ∧ c z ≤ C) (hd : μ ≤ ∑ z, (p z).toReal * c z) :
    ∑ z, (p z).toReal * Real.exp (-c z / C) ≤ rate μ C := by
  have he : 0 ≤ (1 - Real.exp (-1)) / C :=
    div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))) hC.le
  calc
    _ ≤ ∑ z, (p z).toReal * (1 - (1 - Real.exp (-1)) / C * c z) :=
      Finset.sum_le_sum fun z _ =>
        mul_le_mul_of_nonneg_left (exp_neg_chord hC (hc z).1 (hc z).2) ENNReal.toReal_nonneg
    _ = 1 - (1 - Real.exp (-1)) / C * ∑ z, (p z).toReal * c z := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
      rw [pmf_sum_real, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ 1 - (1 - Real.exp (-1)) / C * μ := by gcongr
    _ = rate μ C := by unfold rate; ring

private theorem rate_bounds {μ C : ℝ} (hμ : 0 < μ) (hμC : μ ≤ C) :
    0 < rate μ C ∧ rate μ C < 1 := by
  have hC := lt_of_lt_of_le hμ hμC
  have he := Real.exp_pos (-1)
  have he1 := Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)
  have hm : μ / C ≤ 1 := (div_le_one hC).mpr hμC
  have hm0 : 0 < μ / C := div_pos hμ hC
  dsimp [rate]
  constructor <;> nlinarith

/-- Every forced adaptive query table has geometric Laplace decay under a
uniform conditional drift bound at every full history and source action. -/
theorem adaptive_laplace_decay
    (κ : ∀ n, Record A Y n → A → PMF Y) (π : Policy A Y)
    (c : ∀ n, Record A Y n → A → Y → ℝ)
    {μ C : ℝ} (hμ : 0 < μ) (hμC : μ ≤ C)
    (hc : ∀ n h a y, 0 ≤ c n h a y ∧ c n h a y ≤ C)
    (hd : ∀ n h a, μ ≤ ∑ y, (κ n h a y).toReal * c n h a y)
    (n : ℕ) :
    ∑ h, (historyLaw κ π n h).toReal * Real.exp (-clock c n h / C) ≤ rate μ C ^ n := by
  classical
  have hC : 0 < C := lt_of_lt_of_le hμ hμC
  have hr : 0 ≤ rate μ C := (rate_bounds hμ hμC).1.le
  induction n with
  | zero => simp [historyLaw, clock, PMF.pure_apply]
  | succ n ih =>
      simp only [Record, Fintype.sum_prod_type, clock, neg_add, add_div, Real.exp_add]
      calc
        _ = ∑ h, (historyLaw κ π n h).toReal * Real.exp (-clock c n h / C) *
            (∑ a, (π n h a).toReal * ∑ y, (κ n h a y).toReal *
              Real.exp (-c n h a y / C)) := by
          apply Finset.sum_congr rfl
          intro h _
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro y _
          rw [history_law_succ, ENNReal.toReal_mul, ENNReal.toReal_mul]
          ring
        _ ≤ ∑ h, (historyLaw κ π n h).toReal * Real.exp (-clock c n h / C) *
            rate μ C := by
          apply Finset.sum_le_sum
          intro h _
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
          calc
            _ ≤ ∑ a, (π n h a).toReal * rate μ C :=
              Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
                (row_laplace (κ n h a) (c n h a) hC (hc n h a) (hd n h a))
                ENNReal.toReal_nonneg
            _ = rate μ C := by rw [← Finset.sum_mul, pmf_sum_real, one_mul]
        _ = (∑ h, (historyLaw κ π n h).toReal * Real.exp (-clock c n h / C)) *
            rate μ C := (Finset.sum_mul ..).symm
        _ ≤ rate μ C ^ n * rate μ C := mul_le_mul_of_nonneg_right ih hr
        _ = rate μ C ^ (n + 1) := (pow_succ ..).symm

private theorem low_clock_tail
    (κ : ∀ n, Record A Y n → A → PMF Y) (π : Policy A Y)
    (c : ∀ n, Record A Y n → A → Y → ℝ)
    {μ C : ℝ} (hμ : 0 < μ) (hμC : μ ≤ C)
    (hc : ∀ n h a y, 0 ≤ c n h a y ∧ c n h a y ≤ C)
    (hd : ∀ n h a, μ ≤ ∑ y, (κ n h a y).toReal * c n h a y)
    (n : ℕ) (b : ℝ) :
    ((historyLaw κ π n).toOuterMeasure {h | clock c n h ≤ b}).toReal ≤
      Real.exp (b / C) * rate μ C ^ n := by
  let : MeasurableSpace (Record A Y n) := ⊤
  let : MeasurableSingletonClass (Record A Y n) := ⟨fun _ => trivial⟩
  have hC := lt_of_lt_of_le hμ hμC
  have h := measure_le_le_exp_mul_mgf (μ := (historyLaw κ π n).toMeasure)
    (X := clock c n) b (show -(1 / C) ≤ 0 from neg_nonpos.mpr (div_nonneg zero_le_one hC.le))
    (Integrable.of_finite (f := fun h => Real.exp (-(1 / C) * clock c n h)))
  rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure] at h
  simp only [mgf, PMF.integral_eq_sum, smul_eq_mul] at h
  have he (h : Record A Y n) : Real.exp (-(1 / C) * clock c n h) =
      Real.exp (-clock c n h / C) := by congr 1; ring
  simp_rw [he] at h
  convert h.trans (mul_le_mul_of_nonneg_left
    (adaptive_laplace_decay κ π c hμ hμC hc hd n) (Real.exp_pos _).le) using 1 <;>
    congr 2 <;> ring

/-- Uniform geometric low-clock tails for arbitrary history-dependent source
laws and arbitrary randomized forced query tables. No topology on worlds is used. -/
theorem adaptive_clock_tail
    (κ : ∀ n, Record A Y n → A → PMF Y) (π : Policy A Y)
    (c : ∀ n, Record A Y n → A → Y → ℝ)
    {μ C : ℝ} (hμ : 0 < μ) (hμC : μ ≤ C)
    (hc : ∀ n h a y, 0 ≤ c n h a y ∧ c n h a y ≤ C)
    (hd : ∀ n h a, μ ≤ ∑ y, (κ n h a y).toReal * c n h a y) :
    0 < rate μ C ∧ rate μ C < 1 ∧ 0 < slope μ C ∧
      0 < tailRate μ C ∧ tailRate μ C < 1 ∧
      ∀ n : ℕ, ((historyLaw κ π n).toOuterMeasure
        {h | clock c n h ≤ slope μ C * n}).toReal ≤ tailRate μ C ^ n := by
  have hC := lt_of_lt_of_le hμ hμC
  obtain ⟨hr0, hr1⟩ := rate_bounds hμ hμC
  have hs : 0 < slope μ C := by
    dsimp [slope]
    exact mul_pos_of_neg_of_neg (by linarith) (Real.log_neg hr0 hr1)
  have ht0 : 0 < tailRate μ C := Real.sqrt_pos.mpr hr0
  have ht1 : tailRate μ C < 1 := by
    simpa [tailRate] using (Real.sqrt_lt_sqrt hr0.le hr1)
  refine ⟨hr0, hr1, hs, ht0, ht1, fun n => ?_⟩
  have he : Real.exp (slope μ C * n / C) * rate μ C ^ n = tailRate μ C ^ n := by
    rw [show slope μ C * n / C = (n : ℝ) * (-(Real.log (rate μ C) / 2)) by
      dsimp [slope]; field_simp]
    rw [Real.exp_nat_mul, ← mul_pow]
    congr 1
    rw [← Real.exp_log hr0, ← Real.exp_add]
    convert Real.exp_half (Real.log (rate μ C)) using 1 <;>
      simp [tailRate, Real.exp_log hr0] <;> ring
  exact he ▸ low_clock_tail κ π c hμ hμC hc hd n (slope μ C * n)

/-- Replace the return decision by a fixed next query, preserving all query mass. -/
def forceQueries (a₀ : A) (σ : ∀ n, Record A Y n → PMF (Option A)) : Policy A Y :=
  fun n h => (σ n h).map (fun a => a.getD a₀)

/-- Probability of actually acquiring a specified n-query history before returning.
The decision to return is `none`; the next query is `some a`. -/
def acquiredMass (κ : ∀ n, Record A Y n → A → PMF Y)
    (σ : ∀ n, Record A Y n → PMF (Option A)) : (n : ℕ) → Record A Y n → ℝ
  | 0, _ => 1
  | n + 1, h => acquiredMass κ σ n h.1 *
      (σ n h.1 (some h.2.1)).toReal * (κ n h.1 h.2.1 h.2.2).toReal

private theorem acquired_mass_bounds (κ : ∀ n, Record A Y n → A → PMF Y)
    (σ : ∀ n, Record A Y n → PMF (Option A)) (a₀ : A) (n : ℕ)
    (h : Record A Y n) :
    0 ≤ acquiredMass κ σ n h ∧
      acquiredMass κ σ n h ≤ (historyLaw κ (forceQueries a₀ σ) n h).toReal := by
  classical
  induction n with
  | zero => cases h; simp [acquiredMass, historyLaw, PMF.pure_apply]
  | succ n ih =>
      rcases h with ⟨h, a, y⟩
      have ha : (σ n h (some a)).toReal ≤ (forceQueries a₀ σ n h a).toReal := by
        apply ENNReal.toReal_mono (PMF.apply_ne_top _ _)
        dsimp [forceQueries]
        rw [PMF.map_apply, tsum_fintype]
        simpa using (Finset.single_le_sum (f := fun z : Option A =>
          if a = z.getD a₀ then σ n h z else 0)
          (fun z _ => bot_le) (Finset.mem_univ (some a)))
      dsimp [acquiredMass]
      refine ⟨mul_nonneg (mul_nonneg (ih h).1 ENNReal.toReal_nonneg) ENNReal.toReal_nonneg, ?_⟩
      rw [history_law_succ, ENNReal.toReal_mul, ENNReal.toReal_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (ih h).2 ha ENNReal.toReal_nonneg
          ENNReal.toReal_nonneg) ENNReal.toReal_nonneg

/-- A stopping policy's acquired low-clock prefixes obey the same geometric bound.
The second inequality splits its call-depth tail using the clock already acquired at that depth. -/
theorem stopping_prefix_clock_tail
    (κ : ∀ n, Record A Y n → A → PMF Y)
    (σ : ∀ n, Record A Y n → PMF (Option A)) (a₀ : A)
    (c : ∀ n, Record A Y n → A → Y → ℝ)
    {μ C : ℝ} (hμ : 0 < μ) (hμC : μ ≤ C)
    (hc : ∀ n h a y, 0 ≤ c n h a y ∧ c n h a y ≤ C)
    (hd : ∀ n h a, μ ≤ ∑ y, (κ n h a y).toReal * c n h a y)
    (n : ℕ) :
    (∑ h, if clock c n h ≤ slope μ C * n then acquiredMass κ σ n h else 0) ≤
        tailRate μ C ^ n ∧
    (∑ h, acquiredMass κ σ n h) ≤
      (∑ h, if slope μ C * n ≤ clock c n h then acquiredMass κ σ n h else 0) +
        tailRate μ C ^ n := by
  classical
  have htail := (adaptive_clock_tail κ (forceQueries a₀ σ) c hμ hμC hc hd).2.2.2.2.2 n
  have hm : ∀ h, (if clock c n h ≤ slope μ C * n then historyLaw κ (forceQueries a₀ σ) n h
      else 0) ≠ ⊤ := by intro h; split_ifs <;> simp [PMF.apply_ne_top]
  rw [PMF.toOuterMeasure_apply_fintype] at htail
  simp only [Set.indicator_apply, Set.mem_ofPred_eq] at htail
  rw [ENNReal.toReal_sum (fun h _ => hm h)] at htail
  simp only [apply_ite ENNReal.toReal, ENNReal.toReal_zero] at htail
  have hlo : (∑ h, if clock c n h ≤ slope μ C * n then acquiredMass κ σ n h else 0) ≤
      tailRate μ C ^ n := by
    refine le_trans (Finset.sum_le_sum fun h _ => ?_) htail
    split_ifs
    · exact (acquired_mass_bounds κ σ a₀ n h).2
    · exact le_rfl
  refine ⟨hlo, ?_⟩
  calc
    _ ≤ (∑ h, if slope μ C * n ≤ clock c n h then acquiredMass κ σ n h else 0) +
        (∑ h, if clock c n h ≤ slope μ C * n then acquiredMass κ σ n h else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro h _
      split_ifs <;> have hp := (acquired_mass_bounds κ σ a₀ n h).1 <;> linarith
    _ ≤ _ := by gcongr

/-- The positive increments of the real-order call-count power. -/
def momentWeight (s : ℝ) (n : ℕ) : ℝ≥0∞ :=
  (n + 1 : ℝ≥0∞) ^ s - (n : ℝ≥0∞) ^ s

/-- The geometric correction in the call-clock moment comparison. -/
def momentError (s ρ : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, momentWeight s n * ENNReal.ofReal ρ ^ (n + 1)

private theorem moment_weight_real {s : ℝ} (hs : 0 < s) (n : ℕ) :
    momentWeight s n = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ s - (n : ℝ) ^ s) := by
  rw [ENNReal.ofReal_sub _ (by positivity),
    ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hs.le,
    ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hs.le]
  rw [ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  simp [momentWeight]

private theorem moment_weight_nonneg {s : ℝ} (hs : 0 < s) (n : ℕ) :
    0 ≤ ((n + 1 : ℕ) : ℝ) ^ s - (n : ℝ) ^ s :=
  sub_nonneg.mpr (Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_succ n) hs.le)

private theorem sum_moment_weight {s : ℝ} (hs : 0 < s) (N : ℕ) :
    ∑ n ∈ Finset.range N, momentWeight s n = (N : ℝ≥0∞) ^ s := by
  simp_rw [moment_weight_real hs]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => moment_weight_nonneg hs n),
    Finset.sum_range_sub (fun n : ℕ => (n : ℝ) ^ s) N]
  simp only [Nat.cast_zero, Real.zero_rpow hs.ne', sub_zero]
  rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) hs.le]
  simp

private theorem moment_error_finite {s ρ : ℝ} (hs : 0 < s)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : momentError s ρ < ⊤ := by
  obtain ⟨k, hk⟩ := exists_nat_ge s
  have hnorm : ‖ρ‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hρ0] using hρ1
  have hsum : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * ρ ^ (n + 1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ k * ρ ^ n) 1).2
    (summable_pow_mul_geometric_of_norm_lt_one k hnorm)
  have hsmall : Summable (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) ^ s - (n : ℝ) ^ s) * ρ ^ (n + 1)) := by
    apply hsum.of_nonneg_of_le
    · intro n; exact mul_nonneg (moment_weight_nonneg hs n) (pow_nonneg hρ0 _)
    · intro n
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hρ0 _)
      calc
        _ ≤ ((n + 1 : ℕ) : ℝ) ^ s := sub_le_self _ (Real.rpow_nonneg (by positivity) _)
        _ ≤ ((n + 1 : ℕ) : ℝ) ^ (k : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_cast; omega) hk
        _ = _ := Real.rpow_natCast _ _
  convert hsmall.tsum_ofReal_lt_top using 1
  unfold momentError
  congr 1
  funext n
  rw [moment_weight_real hs, ENNReal.ofReal_mul (moment_weight_nonneg hs n),
    ENNReal.ofReal_pow hρ0]

private theorem weighted_threshold_bound {s : ℝ} (hs : 0 < s) (x : ℝ≥0∞) :
    (∑' n : ℕ, if (n + 1 : ℝ≥0∞) ≤ x then momentWeight s n else 0) ≤ x ^ s := by
  classical
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    by_cases h : (N + 1 : ℝ≥0∞) ≤ x
    · calc
        _ ≤ ∑ n ∈ Finset.range (N + 1), momentWeight s n := by
          apply Finset.sum_le_sum
          intro n _
          split_ifs <;> simp
        _ = (N + 1 : ℝ≥0∞) ^ s := by simpa using sum_moment_weight hs (N + 1)
        _ ≤ x ^ s := ENNReal.rpow_le_rpow h hs.le
    · simpa only [Finset.sum_range_succ, if_neg h, add_zero] using ih

/-- Complete stopped execution paths. Absence of a depth-n record means that
return happened before n acquisitions; the parent law makes return absorbing. -/
structure StoppedPath (A Y : Type) where
  record : (n : ℕ) → Option (Record A Y n)
  root : record 0 = some ()
  parent : ∀ n (h : Record A Y n) a y,
    record (n + 1) = some (h, a, y) → record n = some h

/-- Actual call count, including infinity for a path that never returns. -/
def totalCalls (p : StoppedPath A Y) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ h : Record A Y n, ⨆ (_ : p.record n = some h), (n : ℝ≥0∞)

/-- Actual nonnegative accumulated clock, retaining its value on infinite paths. -/
def totalClock (c : ∀ n, Record A Y n → A → Y → ℝ) (p : StoppedPath A Y) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ h : Record A Y n, ⨆ (_ : p.record n = some h), ENNReal.ofReal (clock c n h)

private theorem path_prefix (p : StoppedPath A Y) {m n : ℕ} (hmn : m ≤ n)
    (hn : ∃ h, p.record n = some h) : ∃ h, p.record m = some h := by
  revert hn
  induction n, hmn using Nat.le_induction with
  | base => exact id
  | succ n _ ih =>
    intro hn
    apply ih
    obtain ⟨⟨h, a, y⟩, hh⟩ := hn
    exact ⟨h, p.parent n h a y hh⟩

private theorem total_calls_power (p : StoppedPath A Y) {s : ℝ} (hs : 0 < s) :
    totalCalls p ^ s = ∑' n : ℕ,
      if ∃ h, p.record (n + 1) = some h then momentWeight s n else 0 := by
  classical
  apply le_antisymm
  · change (ENNReal.orderIsoRpow s hs) (totalCalls p) ≤ _
    unfold totalCalls
    simp only [OrderIso.map_iSup]
    refine iSup_le fun n => iSup_le fun h => iSup_le fun hh => ?_
    change (n : ℝ≥0∞) ^ s ≤ _
    rw [← sum_moment_weight hs n]
    calc
      _ = ∑ j ∈ Finset.range n,
          if ∃ h, p.record (j + 1) = some h then momentWeight s j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [if_pos (path_prefix p (by simpa using Finset.mem_range.mp hj) ⟨h, hh⟩)]
      _ ≤ _ := ENNReal.sum_le_tsum _
  · apply le_trans (ENNReal.tsum_le_tsum fun n => ?_)
      (weighted_threshold_bound hs (totalCalls p))
    by_cases hn : ∃ h, p.record (n + 1) = some h
    · obtain ⟨h, hh⟩ := hn
      have hle : (n + 1 : ℝ≥0∞) ≤ totalCalls p := by
        exact le_iSup_of_le (n + 1) (le_iSup_of_le h (le_iSup_of_le hh (by simp)))
      simp only [if_pos (show ∃ h, p.record (n + 1) = some h from ⟨h, hh⟩), if_pos hle]
      exact le_rfl
    · simp only [if_neg hn]
      exact bot_le

private theorem clock_upper {C : ℝ}
    (c : ∀ n, Record A Y n → A → Y → ℝ)
    (hc : ∀ n h a y, 0 ≤ c n h a y ∧ c n h a y ≤ C)
    (n : ℕ) (h : Record A Y n) : 0 ≤ clock c n h ∧ clock c n h ≤ C * n := by
  induction n with
  | zero => cases h; simp [clock]
  | succ n ih =>
    rcases h with ⟨h, a, y⟩
    have hp := ih h
    have hh := hc n h a y
    simp only [clock, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith

private theorem total_clock_upper {C : ℝ} (hC : 0 < C)
    (c : ∀ n, Record A Y n → A → Y → ℝ)
    (hc : ∀ n h a y, 0 ≤ c n h a y ∧ c n h a y ≤ C)
    (p : StoppedPath A Y) : totalClock c p ≤ ENNReal.ofReal C * totalCalls p := by
  refine iSup_le fun n => iSup_le fun h => iSup_le fun hh => ?_
  calc
    _ ≤ ENNReal.ofReal (C * n) := ENNReal.ofReal_le_ofReal (clock_upper c hc n h).2
    _ = ENNReal.ofReal C * (n : ℝ≥0∞) := by rw [ENNReal.ofReal_mul hC.le]; simp
    _ ≤ _ := by
      gcongr
      exact le_iSup_of_le n (le_iSup_of_le h (le_iSup_of_le hh le_rfl))

/-- A probability execution is identified by the masses of its acquired
cylinders. The whole sample space may carry infinite executions and extra seeds. -/
structure StoppedExecution (κ : ∀ n, Record A Y n → A → PMF Y)
    (σ : ∀ n, Record A Y n → PMF (Option A))
    (Ω : Type*) [MeasurableSpace Ω] where
  law : Measure Ω
  path : Ω → StoppedPath A Y
  measurable_cylinder : ∀ n (P : Record A Y n → Prop),
    MeasurableSet {ω | ∃ h, (path ω).record n = some h ∧ P h}
  cylinder_mass : ∀ n (P : Record A Y n → Prop),
    law {ω | ∃ h, (path ω).record n = some h ∧ P h} =
      ENNReal.ofReal (∑ h, if P h then acquiredMass κ σ n h else 0)

private theorem execution_clock_measurable
    {κ : ∀ n, Record A Y n → A → PMF Y}
    {σ : ∀ n, Record A Y n → PMF (Option A)}
    {Ω : Type*} [MeasurableSpace Ω] (E : StoppedExecution κ σ Ω)
    (c : ∀ n, Record A Y n → A → Y → ℝ) :
    Measurable (fun ω => totalClock c (E.path ω)) := by
  classical
  apply Measurable.iSup
  intro n
  apply Measurable.iSup
  intro h
  have hm : MeasurableSet {ω | (E.path ω).record n = some h} := by
    simpa using E.measurable_cylinder n (fun h' => h' = h)
  convert (measurable_const.indicator hm : Measurable
    ({ω | (E.path ω).record n = some h}.indicator
      (fun _ => ENNReal.ofReal (clock c n h)))) using 1
  funext ω
  by_cases hh : (E.path ω).record n = some h <;> simp [hh, Set.indicator]

private theorem execution_call_tail
    (κ : ∀ n, Record A Y n → A → PMF Y)
    (σ : ∀ n, Record A Y n → PMF (Option A)) (a₀ : A)
    (c : ∀ n, Record A Y n → A → Y → ℝ)
    {μ C : ℝ} (hμ : 0 < μ) (hμC : μ ≤ C)
    (hc : ∀ n h a y, 0 ≤ c n h a y ∧ c n h a y ≤ C)
    (hd : ∀ n h a, μ ≤ ∑ y, (κ n h a y).toReal * c n h a y)
    {Ω : Type*} [MeasurableSpace Ω] (E : StoppedExecution κ σ Ω) (n : ℕ) :
    E.law {ω | ∃ h, (E.path ω).record n = some h} ≤
      E.law {ω | (n : ℝ≥0∞) ≤ totalClock c (E.path ω) / ENNReal.ofReal (slope μ C)} +
        ENNReal.ofReal (tailRate μ C) ^ n := by
  classical
  have hconst := adaptive_clock_tail κ (forceQueries a₀ σ) c hμ hμC hc hd
  have ha := hconst.2.2.1
  have hρ := hconst.2.2.2.1
  calc
    _ = ENNReal.ofReal (∑ h, acquiredMass κ σ n h) := by
      simpa using E.cylinder_mass n (fun _ => True)
    _ ≤ ENNReal.ofReal
        (∑ h, if slope μ C * n ≤ clock c n h then acquiredMass κ σ n h else 0) +
        ENNReal.ofReal (tailRate μ C) ^ n := by
      have hb := ENNReal.ofReal_le_ofReal (stopping_prefix_clock_tail κ σ a₀ c hμ hμC hc hd n).2
      rw [ENNReal.ofReal_add (Finset.sum_nonneg (fun h _ => by
        split_ifs
        · exact (acquired_mass_bounds κ σ a₀ n h).1
        · exact le_rfl))
          (pow_nonneg hρ.le _), ENNReal.ofReal_pow hρ.le] at hb
      exact hb
    _ = E.law {ω | ∃ h, (E.path ω).record n = some h ∧ slope μ C * n ≤ clock c n h} +
        ENNReal.ofReal (tailRate μ C) ^ n := by rw [E.cylinder_mass]
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      apply measure_mono
      rintro ω ⟨h, hh, ht⟩
      apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr ha))
        (Or.inl ENNReal.ofReal_ne_top)).2
      calc
        _ = ENNReal.ofReal (slope μ C * n) := by
          rw [ENNReal.ofReal_mul ha.le]; simp [mul_comm]
        _ ≤ ENNReal.ofReal (clock c n h) := ENNReal.ofReal_le_ofReal ht
        _ ≤ _ := by
          apply le_iSup_of_le n
          apply le_iSup_of_le h
          exact le_iSup (fun _ : (E.path ω).record n = some h =>
            ENNReal.ofReal (clock c n h)) hh

set_option maxHeartbeats 800000 in
-- The dependent history indices and two countable integral interchanges share one proof.
/-- The two extended-real moment comparisons for every realization of the
actual stopped execution cylinders, including nonterminating paths. -/
private theorem execution_moment_bounds
    (κ : ∀ n, Record A Y n → A → PMF Y)
    (σ : ∀ n, Record A Y n → PMF (Option A)) (a₀ : A)
    (c : ∀ n, Record A Y n → A → Y → ℝ)
    {μ C s : ℝ} (hμ : 0 < μ) (hμC : μ ≤ C) (hs : 0 < s)
    (hc : ∀ n h a y, 0 ≤ c n h a y ∧ c n h a y ≤ C)
    (hd : ∀ n h a, μ ≤ ∑ y, (κ n h a y).toReal * c n h a y)
    {Ω : Type*} [MeasurableSpace Ω] (E : StoppedExecution κ σ Ω) :
    (∫⁻ ω, totalClock c (E.path ω) ^ s ∂E.law) ≤
      ENNReal.ofReal C ^ s * ∫⁻ ω, totalCalls (E.path ω) ^ s ∂E.law ∧
    (∫⁻ ω, totalCalls (E.path ω) ^ s ∂E.law) ≤
      ENNReal.ofReal (slope μ C) ^ (-s) *
        (∫⁻ ω, totalClock c (E.path ω) ^ s ∂E.law) + momentError s (tailRate μ C) ∧
    momentError s (tailRate μ C) < ⊤ := by
  classical
  have hC := lt_of_lt_of_le hμ hμC
  have hconst := adaptive_clock_tail κ (forceQueries a₀ σ) c hμ hμC hc hd
  have ha := hconst.2.2.1
  have hρ0 := hconst.2.2.2.1
  have hρ1 := hconst.2.2.2.2.1
  have hT := execution_clock_measurable E c
  have hdiv : Measurable (fun ω => totalClock c (E.path ω) / ENNReal.ofReal (slope μ C)) :=
    hT.div_const _
  have htailset (n : ℕ) : MeasurableSet
      {ω | (n + 1 : ℝ≥0∞) ≤ totalClock c (E.path ω) / ENNReal.ofReal (slope μ C)} :=
    measurableSet_le measurable_const hdiv
  have hsurvive (n : ℕ) : MeasurableSet
      {ω | ∃ h, (E.path ω).record (n + 1) = some h} := by
    simpa using E.measurable_cylinder (n + 1) (fun _ => True)
  refine ⟨?_, ?_, moment_error_finite hs hρ0.le hρ1⟩
  · calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal C ^ s * totalCalls (E.path ω) ^ s ∂E.law := by
        apply lintegral_mono
        intro ω
        simpa only [ENNReal.mul_rpow_of_nonneg _ _ hs.le] using
          ENNReal.rpow_le_rpow (total_clock_upper hC c hc (E.path ω)) hs.le
      _ = _ := lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hs.le ENNReal.ofReal_ne_top)
  · calc
      _ = ∑' n : ℕ, momentWeight s n *
          E.law {ω | ∃ h, (E.path ω).record (n + 1) = some h} := by
        simp_rw [total_calls_power _ hs]
        rw [lintegral_tsum]
        · congr 1; funext n
          simpa only [Set.indicator, Set.mem_ofPred_eq] using
            (lintegral_indicator_const (μ := E.law) (hsurvive n) (momentWeight s n))
        · intro n
          exact (Measurable.ite (hsurvive n) measurable_const measurable_const).aemeasurable
      _ ≤ ∑' n : ℕ, momentWeight s n *
          (E.law {ω | (n + 1 : ℝ≥0∞) ≤ totalClock c (E.path ω) /
            ENNReal.ofReal (slope μ C)} + ENNReal.ofReal (tailRate μ C) ^ (n + 1)) := by
        apply ENNReal.tsum_le_tsum
        intro n
        gcongr
        simpa only [Nat.cast_add, Nat.cast_one] using
          execution_call_tail κ σ a₀ c hμ hμC hc hd E (n + 1)
      _ = (∫⁻ ω, ∑' n : ℕ, if (n + 1 : ℝ≥0∞) ≤ totalClock c (E.path ω) /
          ENNReal.ofReal (slope μ C) then momentWeight s n else 0 ∂E.law) +
          momentError s (tailRate μ C) := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add]
        congr 1
        rw [lintegral_tsum]
        · congr 1; funext n
          simpa only [Set.indicator, Set.mem_ofPred_eq] using
            (lintegral_indicator_const (μ := E.law) (htailset n) (momentWeight s n)).symm
        · intro n
          exact (Measurable.ite (htailset n) measurable_const measurable_const).aemeasurable
      _ ≤ (∫⁻ ω, (totalClock c (E.path ω) / ENNReal.ofReal (slope μ C)) ^ s ∂E.law) +
          momentError s (tailRate μ C) := by
        apply add_le_add _ le_rfl
        exact lintegral_mono fun ω => weighted_threshold_bound hs _
      _ = _ := by
        simp_rw [div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ hs.le,
          ENNReal.inv_rpow, mul_comm, ← ENNReal.rpow_neg]
        rw [lintegral_const_mul _ (hT.pow_const s)]

private def stoppedStep (κ : ∀ n, Record A Y n → A → PMF Y)
    (σ : ∀ n, Record A Y n → PMF (Option A)) (n : ℕ) :
    Option (Record A Y n) → PMF (Option (Record A Y (n + 1)))
  | none => PMF.pure none
  | some h => (σ n h).bind fun a => match a with
    | none => PMF.pure none
    | some a => (κ n h a).map fun y => some (h, a, y)

private def stoppedLaw (κ : ∀ n, Record A Y n → A → PMF Y)
    (σ : ∀ n, Record A Y n → PMF (Option A)) : (n : ℕ) → PMF (Option (Record A Y n))
  | 0 => PMF.pure (some ())
  | n + 1 => (stoppedLaw κ σ n).bind (stoppedStep κ σ n)

private theorem stopped_law_some (κ : ∀ n, Record A Y n → A → PMF Y)
    (σ : ∀ n, Record A Y n → PMF (Option A)) (a₀ : A)
    (n : ℕ) (h : Record A Y n) :
    stoppedLaw κ σ n (some h) = ENNReal.ofReal (acquiredMass κ σ n h) := by
  classical
  induction n with
  | zero => cases h; simp [stoppedLaw, acquiredMass, PMF.pure_apply]
  | succ n ih =>
    rcases h with ⟨h, a, y⟩
    simp only [stoppedLaw, PMF.bind_apply, tsum_fintype, Fintype.sum_option]
    simp [stoppedStep, PMF.bind_apply, PMF.map_apply, PMF.pure_apply, tsum_fintype,
      Fintype.sum_option, Prod.mk.injEq, ite_and, Finset.sum_ite_irrel, mul_ite]
    rw [ih]
    rw [acquiredMass, ENNReal.ofReal_mul
      (mul_nonneg (acquired_mass_bounds κ σ a₀ n h).1 ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul (acquired_mass_bounds κ σ a₀ n h).1]
    simp [ENNReal.ofReal_toReal (PMF.apply_ne_top _ _), mul_assoc]

private theorem trajectory_step_integral
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, Finite (X n)]
    [∀ n, MeasurableSingletonClass (X n)]
    (K : (n : ℕ) → Kernel ((i : ↥(Finset.Iic n)) → X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (K n)] (x₀ : (i : ↥(Finset.Iic 0)) → X i)
    (n : ℕ) (f : X n → X (n + 1) → ℝ≥0∞) :
    (∫⁻ ω, f (ω n) (ω (n + 1)) ∂Kernel.traj K 0 x₀) =
      ∫⁻ ω, ∫⁻ z, f (ω n) z ∂K n (Preorder.frestrictLe n ω)
        ∂Kernel.traj K 0 x₀ := by
  let g := fun z : ((i : ↥(Finset.Iic n)) → X i) × X (n + 1) =>
    f (z.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) z.2
  have hg : Measurable g := measurable_of_countable _
  calc
    _ = ∫⁻ z, g z ∂(Kernel.traj K 0 x₀).map
        (fun ω => (Preorder.frestrictLe n ω, ω (n + 1))) :=
      (lintegral_map hg (by fun_prop)).symm
    _ = ∫⁻ z, g z ∂((Kernel.traj K 0 x₀).map (Preorder.frestrictLe n) ⊗ₘ K n) := by
      rw [Kernel.traj_map_frestrictLe_apply,
        Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le n)]
    _ = ∫⁻ u, ∫⁻ z, g (u, z) ∂K n u ∂(Kernel.traj K 0 x₀).map
        (Preorder.frestrictLe n) := Measure.lintegral_compProd hg
    _ = _ := lintegral_map (measurable_of_countable _) (by fun_prop)

set_option maxHeartbeats 1200000 in
-- The finite marginal induction and almost-sure path restriction share the same trajectory law.
private theorem exists_stopped_execution
    (κ : ∀ n, Record A Y n → A → PMF Y)
    (σ : ∀ n, Record A Y n → PMF (Option A)) (a₀ : A) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      Nonempty (@StoppedExecution A Y _ _ κ σ Ω m) := by
  classical
  letI : (n : ℕ) → MeasurableSpace (Option (Record A Y n)) := fun _ => ⊤
  letI : (n : ℕ) → DiscreteMeasurableSpace (Option (Record A Y n)) := fun _ => inferInstance
  let K : (n : ℕ) → Kernel
      ((i : ↥(Finset.Iic n)) → Option (Record A Y i)) (Option (Record A Y (n + 1))) :=
    fun n => ⟨fun u => (stoppedStep κ σ n (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure,
      measurable_of_countable _⟩
  letI : ∀ n, IsMarkovKernel (K n) := fun n => ⟨fun _ => inferInstanceAs
    (IsProbabilityMeasure (PMF.toMeasure _))⟩
  let x₀ : (i : ↥(Finset.Iic 0)) → Option (Record A Y i) := fun i => by
    obtain ⟨i, hi⟩ := i
    have he : i = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp hi)
    subst i
    exact some ()
  let ν : Measure ((n : ℕ) → Option (Record A Y n)) :=
    Kernel.traj (X := fun n => Option (Record A Y n)) K 0 x₀
  have h0 : ν.map (Preorder.frestrictLe 0) = Measure.dirac x₀ := by
    simpa [ν, Kernel.partialTraj_self, Kernel.id_apply] using Kernel.traj_map_frestrictLe_apply (X := fun n => Option (Record A Y n)) (κ := K) 0 0 x₀
  have hint (n : ℕ) (f : Option (Record A Y n) → ℝ≥0∞) :
      (∫⁻ ω, f (ω n) ∂ν) = ∑ z, f z * stoppedLaw κ σ n z := by
    induction n with
    | zero =>
      calc
        _ = ∫⁻ u, f (u ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∂ν.map (Preorder.frestrictLe 0) :=
          (lintegral_map (measurable_of_countable _) (by fun_prop)).symm
        _ = f (some ()) := by rw [h0, lintegral_dirac' _ (measurable_of_countable _)]
        _ = _ := by simp [stoppedLaw, PMF.pure_apply]
    | succ n ih =>
      rw [trajectory_step_integral (X := fun n => Option (Record A Y n)) K x₀ n (fun _ z => f z)]
      change (∫⁻ ω, (∫⁻ z, f z ∂(stoppedStep κ σ n (ω n)).toMeasure) ∂ν) = _
      rw [ih (fun x => ∫⁻ z, f z ∂(stoppedStep κ σ n x).toMeasure)]
      simp only [lintegral_fintype, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        stoppedLaw, PMF.bind_apply, tsum_fintype, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x _
      ac_rfl
  have hprob (n : ℕ) (P : Option (Record A Y n) → Prop) :
      ν {ω | P (ω n)} = ∑ z, if P z then stoppedLaw κ σ n z else 0 := by
    have hm : MeasurableSet {ω : (n : ℕ) → Option (Record A Y n) | P (ω n)} :=
      (MeasurableSet.of_discrete : MeasurableSet {z | P z}).preimage (measurable_pi_apply n)
    rw [← lintegral_indicator_one hm]
    change (∫⁻ ω, if P (ω n) then 1 else 0 ∂ν) = _
    rw [hint n (fun z => if P z then 1 else 0)]
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> simp
  let V : Set ((n : ℕ) → Option (Record A Y n)) :=
    {ω | ω 0 = some () ∧ ∀ n (h : Record A Y n) a y,
      ω (n + 1) = some (h, a, y) → ω n = some h}
  have hVm : MeasurableSet V := by
    simp only [V, Set.ofPred_and, Set.ofPred_forall, imp_iff_not_or, Set.ofPred_or]
    refine (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter ?_
    refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun h =>
      MeasurableSet.iInter fun a => MeasurableSet.iInter fun y => ?_
    exact (measurableSet_eq_fun (measurable_pi_apply (n + 1)) measurable_const).compl.union
      (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)
  have hroot : ∀ᵐ ω ∂ν, ω 0 = some () := by
    rw [ae_iff]
    simpa [stoppedLaw, PMF.pure_apply] using hprob 0 (fun z => z ≠ some ())
  have hparent (n : ℕ) (h : Record A Y n) (a : A) (y : Y) :
      ∀ᵐ ω ∂ν, ω (n + 1) = some (h, a, y) → ω n = some h := by
    rw [ae_iff]
    have hm : MeasurableSet {ω : (n : ℕ) → Option (Record A Y n) |
        ω (n + 1) = some (h, a, y) ∧ ω n ≠ some h} :=
      (measurableSet_eq_fun (measurable_pi_apply (n + 1)) measurable_const).inter
        (measurableSet_eq_fun (measurable_pi_apply n) measurable_const).compl
    change ν {ω | ¬ (ω (n + 1) = some (h, a, y) → ω n = some h)} = 0
    simp only [Classical.not_imp]
    rw [← lintegral_indicator_one hm]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    rw [trajectory_step_integral (X := fun n => Option (Record A Y n)) K x₀ n
      (fun x z => if z = some (h, a, y) ∧ x ≠ some h then 1 else 0)]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards with ω
    change (∫⁻ z, (if z = some (h, a, y) ∧ ω n ≠ some h then 1 else 0)
      ∂(stoppedStep κ σ n (ω n)).toMeasure) = 0
    rw [lintegral_fintype]
    cases hx : ω n with
    | none => simp [stoppedStep, PMF.pure_apply, PMF.toMeasure_apply_singleton]
    | some q =>
      by_cases hq : q = h
      · subst q; simp
      · simp [stoppedStep, PMF.bind_apply, PMF.map_apply, PMF.pure_apply,
          PMF.toMeasure_apply_singleton, tsum_fintype, Fintype.sum_option,
          hq, Ne.symm hq, Prod.mk.injEq, ite_and, Finset.sum_ite_irrel, mul_ite]
  have hV : ∀ᵐ ω ∂ν, ω ∈ V := by
    apply hroot.and
    simp only [ae_all_iff]
    exact hparent
  refine ⟨V, inferInstance, ⟨{
    law := ν.comap Subtype.val
    path := fun ω => ⟨ω.1, ω.2.1, ω.2.2⟩
    measurable_cylinder := ?_
    cylinder_mass := ?_ }⟩⟩
  · intro n P
    have hm : MeasurableSet {ω : (n : ℕ) → Option (Record A Y n) |
        ∃ h, ω n = some h ∧ P h} :=
      (MeasurableSet.of_discrete : MeasurableSet {z | ∃ h, z = some h ∧ P h}).preimage
        (measurable_pi_apply n)
    exact hm.preimage measurable_subtype_coe
  · intro n P
    rw [comap_subtype_coe_apply hVm]
    have himage : Subtype.val '' {ω : V | ∃ h, ω.1 n = some h ∧ P h} =
        {ω | ∃ h, ω n = some h ∧ P h} ∩ V := by
      ext ω
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨z, hz, rfl⟩; exact ⟨hz, z.2⟩
      · rintro ⟨hp, hv⟩; exact ⟨⟨ω, hv⟩, hp, rfl⟩
    rw [himage, Set.inter_comm _ V, Measure.measure_inter_eq_of_ae hV,
      hprob n (fun z => ∃ h, z = some h ∧ P h)]
    simp only [Fintype.sum_option]
    simp only [Option.some.injEq, reduceCtorEq, false_and,
      exists_false, if_false, zero_add]
    rw [ENNReal.ofReal_sum_of_nonneg (fun h _ => by
      split_ifs
      · exact (acquired_mass_bounds κ σ a₀ n h).1
      · exact le_rfl)]
    apply Finset.sum_congr rfl
    intro h _
    have he : (∃ q, h = q ∧ P q) ↔ P h := by
      constructor
      · rintro ⟨q, rfl, hp⟩; exact hp
      · intro hp; exact ⟨h, rfl, hp⟩
    simp only [he]
    split_ifs <;> simp [stopped_law_some κ σ a₀]

/-- Arbitrary families of actual worlds and requests obey the same two moment
bounds and the same uniform-finiteness equivalence, for every positive real order. -/
theorem stopped_clock_moment_comparison
    {I : Type*}
    (κ : ∀ i : I, ∀ n, Record A Y n → A → PMF Y)
    (σ : ∀ i : I, ∀ n, Record A Y n → PMF (Option A)) (a₀ : A)
    (c : ∀ i : I, ∀ n, Record A Y n → A → Y → ℝ)
    {μ C s : ℝ} (hμ : 0 < μ) (hμC : μ ≤ C) (hs : 0 < s)
    (hc : ∀ i n h a y, 0 ≤ c i n h a y ∧ c i n h a y ≤ C)
    (hd : ∀ i n h a, μ ≤ ∑ y, (κ i n h a y).toReal * c i n h a y)
    :
    momentError s (tailRate μ C) < ⊤ ∧
    (∀ i, ∃ (Ξ : Type) (m : MeasurableSpace Ξ),
      Nonempty (@StoppedExecution A Y _ _ (κ i) (σ i) Ξ m)) ∧
    (∀ (Ω : I → Type*) [∀ i, MeasurableSpace (Ω i)]
      (E : ∀ i, StoppedExecution (κ i) (σ i) (Ω i)),
    (∀ i,
      (∫⁻ ω, totalClock (c i) ((E i).path ω) ^ s ∂(E i).law) ≤
        ENNReal.ofReal C ^ s * ∫⁻ ω, totalCalls ((E i).path ω) ^ s ∂(E i).law ∧
      (∫⁻ ω, totalCalls ((E i).path ω) ^ s ∂(E i).law) ≤
        ENNReal.ofReal (slope μ C) ^ (-s) *
          (∫⁻ ω, totalClock (c i) ((E i).path ω) ^ s ∂(E i).law) + momentError s (tailRate μ C)) ∧
    ((⨆ i, ∫⁻ ω, totalClock (c i) ((E i).path ω) ^ s ∂(E i).law) < ⊤ ↔
      (⨆ i, ∫⁻ ω, totalCalls ((E i).path ω) ^ s ∂(E i).law) < ⊤)) := by
  have hC := lt_of_lt_of_le hμ hμC
  have hr := rate_bounds hμ hμC
  have ha : 0 < slope μ C := by
    dsimp [slope]
    exact mul_pos_of_neg_of_neg (by linarith) (Real.log_neg hr.1 hr.2)
  have hρ0 : 0 ≤ tailRate μ C := Real.sqrt_nonneg _
  have hρ1 : tailRate μ C < 1 := by
    simpa [tailRate] using Real.sqrt_lt_sqrt hr.1.le hr.2
  have herr := moment_error_finite hs hρ0 hρ1
  refine ⟨herr, fun i => exists_stopped_execution (κ i) (σ i) a₀, ?_⟩
  intro Ω m E
  have hb (i : I) := execution_moment_bounds (κ i) (σ i) a₀ (c i)
    hμ hμC hs (hc i) (hd i) (E i)
  refine ⟨fun i => ⟨(hb i).1, (hb i).2.1⟩, ?_⟩
  have hCf : ENNReal.ofReal C ^ s < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg hs.le ENNReal.ofReal_ne_top
  have haf : ENNReal.ofReal (slope μ C) ^ (-s) < ⊤ := by
    rw [ENNReal.ofReal_rpow_of_pos ha]
    exact ENNReal.ofReal_lt_top
  constructor
  · intro ht
    apply lt_of_le_of_lt (iSup_le fun i => (hb i).2.1.trans ?_)
      (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top haf ht, herr⟩)
    gcongr
    exact le_iSup (fun i => ∫⁻ ω, totalClock (c i) ((E i).path ω) ^ s ∂(E i).law) i
  · intro hm
    apply lt_of_le_of_lt (iSup_le fun i => (hb i).1.trans ?_)
      (ENNReal.mul_lt_top hCf hm)
    gcongr
    exact le_iSup (fun i => ∫⁻ ω, totalCalls ((E i).path ω) ^ s ∂(E i).law) i

end D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison
