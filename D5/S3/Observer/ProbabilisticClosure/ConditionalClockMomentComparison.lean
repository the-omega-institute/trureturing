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

noncomputable section

open scoped ENNReal BigOperators
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

end D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison
