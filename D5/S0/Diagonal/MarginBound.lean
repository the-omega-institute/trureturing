/- GID: D5/S0/Diagonal/MarginBound
   generality: G
   mirror-B: D5/B/S0/Diagonal/MarginBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: KL-Chernoff bound for finite diagonal listings with a linear row margin. -/

import D5.S0.Diagonal.DistanceProfile
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.Basic

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory unitInterval

universe u v

namespace D5.S0.Diagonal.MarginBound

open DistanceProfile

variable {A : Type u} {Y : Type v}

/-- The scalar Kullback--Leibler divergence between Bernoulli parameters. -/
noncomputable def bernoulliKL (q p : ℝ) : ℝ :=
  q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p))

/-- Bernoulli KL divergence vanishes on the diagonal inside the open unit interval. -/
@[simp] theorem bernoulliKL_self {p : ℝ} (hp : 0 < p) (hp_one : p < 1) :
    bernoulliKL p p = 0 := by
  simp [bernoulliKL, hp.ne', (sub_pos.mpr hp_one).ne']

/-- Bernoulli KL is continuous while both parameters stay strictly between zero and one. -/
theorem continuousAt_bernoulliKL {q p : ℝ} (hq : 0 < q) (hq_one : q < 1)
    (hp : 0 < p) (hp_one : p < 1) :
    ContinuousAt (fun z : ℝ × ℝ => bernoulliKL z.1 z.2) (q, p) := by
  have hq_div : q / p ≠ 0 := div_ne_zero hq.ne' hp.ne'
  have hc_div : (1 - q) / (1 - p) ≠ 0 :=
    div_ne_zero (sub_pos.mpr hq_one).ne' (sub_pos.mpr hp_one).ne'
  have hp_ne : p ≠ 0 := hp.ne'
  have hpc_ne : 1 - p ≠ 0 := (sub_pos.mpr hp_one).ne'
  unfold bernoulliKL
  fun_prop (disch := simp_all)

/-- Bernoulli KL is nonnegative on the open unit square. -/
theorem bernoulliKL_nonneg {q p : ℝ} (hq : 0 < q) (hq_one : q < 1)
    (hp : 0 < p) (hp_one : p < 1) : 0 ≤ bernoulliKL q p := by
  have hq0 : 0 ≤ q / p := (div_pos hq hp).le
  have hq1 := Real.self_sub_one_le_mul_log hq0
  have hc0 : 0 ≤ (1 - q) / (1 - p) :=
    (div_pos (sub_pos.mpr hq_one) (sub_pos.mpr hp_one)).le
  have hc1 := Real.self_sub_one_le_mul_log hc0
  have hp0 : 0 < p := hp
  have hpc0 : 0 < 1 - p := sub_pos.mpr hp_one
  rw [bernoulliKL]
  apply le_of_sub_nonneg
  calc
    q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p)) - 0 =
        p * ((q / p) * Real.log (q / p)) +
          (1 - p) * (((1 - q) / (1 - p)) * Real.log ((1 - q) / (1 - p))) := by
            field_simp
            ring
    _ ≥ p * (q / p - 1) + (1 - p) * ((1 - q) / (1 - p) - 1) := by
      gcongr
    _ = 0 := by
      field_simp
      ring

/-- Bernoulli KL is strictly positive away from the diagonal. -/
theorem bernoulliKL_pos {q p : ℝ} (hq : 0 < q) (hq_one : q < 1)
    (hp : 0 < p) (hp_one : p < 1) (hqp : q ≠ p) : 0 < bernoulliKL q p := by
  have hq0 : 0 ≤ q / p := (div_pos hq hp).le
  have hq_ne : q / p ≠ 1 := by
    exact div_ne_one_of_ne hqp
  have hq1 := Real.self_sub_one_lt_mul_log hq0 hq_ne
  have hc0 : 0 ≤ (1 - q) / (1 - p) :=
    (div_pos (sub_pos.mpr hq_one) (sub_pos.mpr hp_one)).le
  have hc1 := Real.self_sub_one_le_mul_log hc0
  have hp0 : 0 < p := hp
  have hpc0 : 0 < 1 - p := sub_pos.mpr hp_one
  rw [bernoulliKL]
  calc
    0 = p * (q / p - 1) + (1 - p) * ((1 - q) / (1 - p) - 1) := by
      field_simp
      ring
    _ < p * ((q / p) * Real.log (q / p)) +
        (1 - p) * ((1 - q) / (1 - p) - 1) := by
      simpa only [add_comm] using
        add_lt_add_right (mul_lt_mul_of_pos_left hq1 hp)
          ((1 - p) * ((1 - q) / (1 - p) - 1))
    _ ≤ p * ((q / p) * Real.log (q / p)) +
        (1 - p) * (((1 - q) / (1 - p)) * Real.log ((1 - q) / (1 - p))) := by
      simpa only [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_left hc1 hpc0.le)
          (p * ((q / p) * Real.log (q / p)))
    _ = q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p)) := by
      field_simp

/-- The moment generating function of `Bin(r,p)` has its usual closed form. -/
theorem binomial_mgf (r : ℕ) (p : Set.Icc (0 : ℝ) 1) (t : ℝ) :
    mgf id Bin(ℝ, r, p) t = (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ r := by
  rw [mgf, integral_map_cast_binomial]
  simp only [id_eq, smul_eq_mul]
  rw [show Finset.Iic r = Finset.range (r + 1) by ext k; simp]
  calc
    (∑ k ∈ Finset.range (r + 1),
        (↑(r.choose k) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (r - k)) *
          Real.exp (t * (k : ℝ))) =
        ∑ k ∈ Finset.range (r + 1),
          ((p : ℝ) * Real.exp t) ^ k * (1 - (p : ℝ)) ^ (r - k) * r.choose k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [mul_comm t (k : ℝ), Real.exp_nat_mul]
      ring
    _ = ((p : ℝ) * Real.exp t + (1 - (p : ℝ))) ^ r := (add_pow _ _ _).symm
    _ = (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ r := by ring

/-- The KL-Chernoff lower tail for a binomial random variable. -/
theorem binomial_lower_tail_kl (r : ℕ) {q : ℝ} (p : Set.Icc (0 : ℝ) 1)
    (hq : 0 < q) (hqp : q < (p : ℝ)) (hp_one : (p : ℝ) < 1) :
    Bin(ℝ, r, p).real {x | x ≤ q * r} ≤
      Real.exp (-(r : ℝ) * bernoulliKL q p) := by
  have hp : 0 < (p : ℝ) := hq.trans hqp
  have hq_one : q < 1 := hqp.trans hp_one
  have hqc : 0 < 1 - q := sub_pos.mpr hq_one
  have hpc : 0 < 1 - (p : ℝ) := sub_pos.mpr hp_one
  let t := Real.log (q * (1 - (p : ℝ)) / ((p : ℝ) * (1 - q)))
  have hratio_pos : 0 < q * (1 - (p : ℝ)) / ((p : ℝ) * (1 - q)) := by
    positivity
  have hratio_le : q * (1 - (p : ℝ)) / ((p : ℝ) * (1 - q)) ≤ 1 := by
    rw [div_le_one (mul_pos hp hqc)]
    nlinarith
  have ht : t ≤ 0 := Real.log_nonpos hratio_pos.le hratio_le
  have h_int : Integrable (fun x : ℝ => Real.exp (t * id x)) Bin(ℝ, r, p) :=
    integrable_map_cast_binomial _
  have hchernoff := measure_le_le_exp_mul_mgf
    (μ := Bin(ℝ, r, p)) (X := id) (t := t) (q * r) ht h_int
  have hexp : Real.exp t = q * (1 - (p : ℝ)) / ((p : ℝ) * (1 - q)) := by
    change Real.exp (Real.log (q * (1 - (p : ℝ)) / ((p : ℝ) * (1 - q)))) = _
    rw [Real.exp_log hratio_pos]
  have hbase : 1 - (p : ℝ) + (p : ℝ) * Real.exp t =
      (1 - (p : ℝ)) / (1 - q) := by
    rw [hexp]
    field_simp
    ring
  have ht_log : t = Real.log (q / (p : ℝ)) -
      Real.log ((1 - q) / (1 - (p : ℝ))) := by
    change Real.log (q * (1 - (p : ℝ)) / ((p : ℝ) * (1 - q))) = _
    rw [Real.log_div (mul_ne_zero hq.ne' hpc.ne') (mul_ne_zero hp.ne' hqc.ne'),
      Real.log_mul hq.ne' hpc.ne', Real.log_mul hp.ne' hqc.ne',
      Real.log_div hq.ne' hp.ne', Real.log_div hqc.ne' hpc.ne']
    ring
  have hbase_log : Real.log ((1 - (p : ℝ)) / (1 - q)) =
      -Real.log ((1 - q) / (1 - (p : ℝ))) := by
    rw [Real.log_div hpc.ne' hqc.ne', Real.log_div hqc.ne' hpc.ne']
    ring
  have hbase_pow : ((1 - (p : ℝ)) / (1 - q)) ^ r =
      Real.exp ((r : ℝ) * Real.log ((1 - (p : ℝ)) / (1 - q))) := by
    calc
      ((1 - (p : ℝ)) / (1 - q)) ^ r =
          Real.exp (Real.log ((1 - (p : ℝ)) / (1 - q))) ^ r := by
        rw [Real.exp_log (div_pos hpc hqc)]
      _ = _ := (Real.exp_nat_mul _ r).symm
  calc
    Bin(ℝ, r, p).real {x | x ≤ q * r} ≤
        Real.exp (-t * (q * r)) * mgf id Bin(ℝ, r, p) t := by
      simpa only [id_eq] using hchernoff
    _ = Real.exp (-t * (q * r)) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ r := by rw [binomial_mgf]
    _ = Real.exp (-t * (q * r)) * ((1 - (p : ℝ)) / (1 - q)) ^ r := by
      rw [hbase]
    _ = Real.exp (-t * (q * r)) *
        Real.exp ((r : ℝ) * Real.log ((1 - (p : ℝ)) / (1 - q))) := by
      rw [hbase_pow]
    _ = Real.exp
        (-t * (q * r) + (r : ℝ) * Real.log ((1 - (p : ℝ)) / (1 - q))) := by
      rw [Real.exp_add]
    _ = Real.exp (-(r : ℝ) * bernoulliKL q p) := by
      rw [ht_log, hbase_log, bernoulliKL]
      ring_nf

/-- The unnormalized lower prefix of a binomial count with `c` nonzero choices. -/
def binomialPrefixCount (r c s : ℕ) : ℕ :=
  ∑ j ∈ Finset.range s, r.choose j * c ^ j

private noncomputable def binomialParameter (y : ℕ) (hy : 1 ≤ y) : Set.Icc (0 : ℝ) 1 :=
  ⟨((y : ℝ) - 1) / y, by
    constructor
    · exact div_nonneg (by exact_mod_cast Nat.zero_le (y - 1)) (Nat.cast_nonneg y)
    · rw [div_le_one (by exact_mod_cast Nat.zero_lt_of_lt hy)]
      linarith⟩

@[simp] private theorem binomialPrefixCount_full (r c : ℕ) :
    binomialPrefixCount r c (r + 1) = (1 + c) ^ r := by
  simpa [binomialPrefixCount, mul_comm, add_comm] using (add_pow c 1 r).symm

private theorem binomial_prefix_ratio (r y : ℕ) (t : ℝ) (hy : 1 ≤ y)
    (hs : Nat.ceil t ≤ r + 1) :
    (binomialPrefixCount r (y - 1) (Nat.ceil t) : ℝ) / (y : ℝ) ^ r =
      Bin(ℝ, r, binomialParameter y hy).real {x | x < t} := by
  have hy_pos : (0 : ℝ) < y := by exact_mod_cast Nat.zero_lt_of_lt hy
  have hy_ne : (y : ℝ) ≠ 0 := hy_pos.ne'
  have hp_compl : 1 - (binomialParameter y hy : ℝ) = 1 / (y : ℝ) := by
    change 1 - ((y : ℝ) - 1) / y = 1 / y
    field_simp
    ring
  have hsubset : Finset.range (Nat.ceil t) ⊆ Finset.Iic r := by
    intro k hk
    simp only [Finset.mem_range, Finset.mem_Iic] at hk ⊢
    omega
  have hmeasure :
      Bin(ℝ, r, binomialParameter y hy).real {x | x < t} =
        ∑ k ∈ Finset.range (Nat.ceil t),
          (r.choose k : ℝ) * (binomialParameter y hy : ℝ) ^ k *
            (1 - (binomialParameter y hy : ℝ)) ^ (r - k) := by
    calc
      Bin(ℝ, r, binomialParameter y hy).real {x | x < t} =
          ∫ x, {x : ℝ | x < t}.indicator 1 x
            ∂Bin(ℝ, r, binomialParameter y hy) := by
        rw [integral_indicator_one]
        exact measurableSet_lt measurable_id measurable_const
      _ = ∑ k ∈ Finset.Iic r,
          ((r.choose k : ℝ) * (binomialParameter y hy : ℝ) ^ k *
            (1 - (binomialParameter y hy : ℝ)) ^ (r - k)) •
              {x : ℝ | x < t}.indicator 1 (k : ℝ) :=
        integral_map_cast_binomial _
      _ = ∑ k ∈ Finset.range (Nat.ceil t),
          ((r.choose k : ℝ) * (binomialParameter y hy : ℝ) ^ k *
            (1 - (binomialParameter y hy : ℝ)) ^ (r - k)) •
              {x : ℝ | x < t}.indicator 1 (k : ℝ) := by
        symm
        apply Finset.sum_subset hsubset
        intro k hkr hk
        have hsk : Nat.ceil t ≤ k := Nat.le_of_not_gt (by simpa using hk)
        have hknot : (k : ℝ) ∉ {x : ℝ | x < t} := by
          simpa only [Set.mem_setOf_eq, Nat.lt_ceil] using not_lt_of_ge hsk
        rw [Set.indicator_of_notMem hknot]
        simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        have hks : k < Nat.ceil t := Finset.mem_range.mp hk
        have hkmem : (k : ℝ) ∈ {x : ℝ | x < t} := by
          simpa only [Set.mem_setOf_eq, Nat.lt_ceil] using hks
        rw [Set.indicator_of_mem hkmem]
        simp
  rw [hmeasure, binomialPrefixCount, Nat.cast_sum, Finset.sum_div]
  simp only [Nat.cast_mul, Nat.cast_pow]
  apply Finset.sum_congr rfl
  intro k hk
  have hkr : k ≤ r := Finset.mem_Iic.mp (hsubset hk)
  rw [Nat.cast_sub hy, hp_compl]
  simp only [binomialParameter, Nat.cast_one]
  change (r.choose k : ℝ) * ((y : ℝ) - 1) ^ k / (y : ℝ) ^ r =
    (r.choose k : ℝ) * (((y : ℝ) - 1) / y) ^ k * (1 / (y : ℝ)) ^ (r - k)
  rw [div_pow, one_div, inv_pow]
  field_simp
  rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hkr]

private theorem row_prefix_count [Fintype A] [Fintype Y] (f : Y → Y) (s : ℕ) :
    (∑ j ∈ Finset.range s, rowDistanceCount (A := A) f j) =
      Nat.card {y : Y // f y = y} *
          binomialPrefixCount (Fintype.card A - 1) (Fintype.card Y - 1) s +
        (Fintype.card Y - Nat.card {y : Y // f y = y}) *
          binomialPrefixCount (Fintype.card A - 1) (Fintype.card Y - 1) (s - 1) := by
  induction s with
  | zero => simp [binomialPrefixCount]
  | succ s ih =>
      cases s with
      | zero => simp [binomialPrefixCount, rowDistanceCount]
      | succ s =>
          rw [Finset.sum_range_succ, ih]
          simp only [rowDistanceCount, Nat.succ_ne_zero, if_false, Nat.succ_sub_one,
            binomialPrefixCount, Finset.sum_range_succ]
          ring

private theorem binomialPrefixCount_pred_le (r c s : ℕ) :
    binomialPrefixCount r c (s - 1) ≤ binomialPrefixCount r c s := by
  cases s with
  | zero => simp [binomialPrefixCount]
  | succ s =>
      simp only [Nat.succ_sub_one, binomialPrefixCount, Finset.sum_range_succ]
      exact Nat.le_add_right _ _

/-- A row lower prefix is dominated by the corresponding `Bin(|A|-1,(|Y|-1)/|Y|)`
prefix after accounting for its freely chosen diagonal value. -/
theorem row_prefix_le_binomial [Fintype A] [Fintype Y] (f : Y → Y) (s : ℕ) :
    (∑ j ∈ Finset.range s, rowDistanceCount (A := A) f j) ≤
      Fintype.card Y *
        binomialPrefixCount (Fintype.card A - 1) (Fintype.card Y - 1) s := by
  classical
  let fixed := Nat.card {y : Y // f y = y}
  let total := Fintype.card Y
  let pref := binomialPrefixCount (Fintype.card A - 1) (Fintype.card Y - 1) s
  let previous :=
    binomialPrefixCount (Fintype.card A - 1) (Fintype.card Y - 1) (s - 1)
  have hfixed : fixed ≤ total := by
    dsimp [fixed, total]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  have hprevious : previous ≤ pref := binomialPrefixCount_pred_le _ _ _
  rw [row_prefix_count]
  change fixed * pref + (total - fixed) * previous ≤ total * pref
  calc
    fixed * pref + (total - fixed) * previous ≤
        fixed * pref + (total - fixed) * pref := by gcongr
    _ = total * pref := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hfixed]

private theorem row_prefix_total [Fintype A] [Fintype Y] (f : Y → Y)
    (hA : 1 ≤ Fintype.card A) (hY : 1 ≤ Fintype.card Y) :
    (∑ j ∈ Finset.range (Fintype.card A + 1), rowDistanceCount (A := A) f j) =
      Fintype.card Y ^ Fintype.card A := by
  classical
  let m := Fintype.card A
  let y := Fintype.card Y
  let fixed := Nat.card {z : Y // f z = z}
  have hm : m - 1 + 1 = m := Nat.sub_add_cancel hA
  have hy : 1 + (y - 1) = y := Nat.add_sub_of_le hY
  have hfixed : fixed ≤ y := by
    dsimp [fixed, y]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  have hfull : binomialPrefixCount (m - 1) (y - 1) m = y ^ (m - 1) := by
    simpa only [hm, hy] using binomialPrefixCount_full (m - 1) (y - 1)
  have hextra :
      binomialPrefixCount (m - 1) (y - 1) (m + 1) =
        binomialPrefixCount (m - 1) (y - 1) m := by
    simp only [binomialPrefixCount, Finset.sum_range_succ]
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [row_prefix_count]
  change fixed * binomialPrefixCount (m - 1) (y - 1) (m + 1) +
      (y - fixed) * binomialPrefixCount (m - 1) (y - 1) (m + 1 - 1) = y ^ m
  rw [hextra, Nat.add_one_sub_one, hfull, ← Nat.add_mul, Nat.add_sub_of_le hfixed]
  rw [← pow_succ', hm]

private theorem row_tail_add_prefix [Fintype A] [Fintype Y] (f : Y → Y) (s : ℕ)
    (hA : 1 ≤ Fintype.card A) (hY : 1 ≤ Fintype.card Y)
    (hs : s ≤ Fintype.card A + 1) :
    (∑ j ∈ Finset.Icc s (Fintype.card A), rowDistanceCount (A := A) f j) +
        (∑ j ∈ Finset.range s, rowDistanceCount (A := A) f j) =
      Fintype.card Y ^ Fintype.card A := by
  rw [← row_prefix_total f hA hY]
  rw [← Finset.Ico_succ_right_eq_Icc]
  change (∑ j ∈ Finset.Ico s (Fintype.card A + 1),
      rowDistanceCount (A := A) f j) +
      (∑ j ∈ Finset.range s, rowDistanceCount (A := A) f j) = _
  simpa only [add_comm] using
    Finset.sum_range_add_sum_Ico (fun j => rowDistanceCount (A := A) f j) hs

/-- The finite uniform probability that some listing row misses the prescribed linear margin. -/
noncomputable def marginFailureProbability [Fintype A] [Fintype Y]
    (f : Y → Y) (alpha : ℝ) : ℝ :=
  Nat.card {g : A → A → Y //
      ∃ a, (hammingDistance f g a : ℝ) < alpha * Fintype.card A} /
    Nat.card (A → A → Y)

private theorem marginFailureProbability_eq_one_sub_pow [Fintype A] [Fintype Y]
    (f : Y → Y) (alpha : ℝ) (hA : 1 ≤ Fintype.card A) (hY : 1 ≤ Fintype.card Y)
    (hs : Nat.ceil (alpha * Fintype.card A) ≤ Fintype.card A + 1) :
    marginFailureProbability (A := A) f alpha =
      1 - (((∑ j ∈ Finset.Icc (Nat.ceil (alpha * Fintype.card A)) (Fintype.card A),
          rowDistanceCount (A := A) f j : ℕ) : ℝ) /
            (Fintype.card Y : ℝ) ^ Fintype.card A) ^ Fintype.card A := by
  classical
  let s := Nat.ceil (alpha * Fintype.card A)
  let tail := ∑ j ∈ Finset.Icc s (Fintype.card A), rowDistanceCount (A := A) f j
  let total := Fintype.card Y ^ Fintype.card A
  let good : (A → A → Y) → Prop := fun g => ∀ a, s ≤ hammingDistance f g a
  let failure : (A → A → Y) → Prop := fun g =>
    ∃ a, (hammingDistance f g a : ℝ) < alpha * Fintype.card A
  let e : {g : A → A → Y // failure g} ≃ {g : A → A → Y // ¬good g} :=
    (Equiv.refl (A → A → Y)).subtypeEquiv fun g => by
      dsimp [failure, good, s]
      constructor
      · rintro ⟨a, ha⟩ hall
        exact Nat.not_lt_of_ge (hall a) (Nat.lt_ceil.mpr ha)
      · intro h
        push Not at h
        rcases h with ⟨a, ha⟩
        exact ⟨a, Nat.lt_ceil.mp ha⟩
  have hsplit : tail +
      (∑ j ∈ Finset.range s, rowDistanceCount (A := A) f j) = total := by
    exact row_tail_add_prefix f s hA hY hs
  have htail : tail ≤ total := by omega
  have htotal_pos : 0 < total := by
    dsimp [total]
    positivity
  have htotal_card : Nat.card (A → A → Y) = total ^ Fintype.card A := by
    dsimp [total]
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun]
  have hgood_card : Nat.card {g : A → A → Y // good g} = tail ^ Fintype.card A := by
    dsimp [good, tail, s]
    exact min_distance_tail f (Nat.ceil (alpha * Fintype.card A))
  have hfailure_card :
      Nat.card {g : A → A → Y // failure g} =
        total ^ Fintype.card A - tail ^ Fintype.card A := by
    calc
      Nat.card {g : A → A → Y // failure g} =
          Nat.card {g : A → A → Y // ¬good g} := Nat.card_congr e
      _ = Nat.card (A → A → Y) - Nat.card {g : A → A → Y // good g} := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
      _ = _ := by rw [htotal_card, hgood_card]
  rw [marginFailureProbability, show
    Nat.card {g : A → A → Y //
        ∃ a, (hammingDistance f g a : ℝ) < alpha * Fintype.card A} =
      total ^ Fintype.card A - tail ^ Fintype.card A by exact hfailure_card,
    htotal_card]
  change ((total ^ Fintype.card A - tail ^ Fintype.card A : ℕ) : ℝ) /
      (total ^ Fintype.card A : ℕ) =
        1 - ((tail : ℝ) / (Fintype.card Y : ℝ) ^ Fintype.card A) ^
          Fintype.card A
  have htotal_cast : (total : ℝ) = (Fintype.card Y : ℝ) ^ Fintype.card A := by
    simp [total]
  rw [← htotal_cast]
  rw [Nat.cast_sub (pow_le_pow_left' htail _)]
  simp only [Nat.cast_pow]
  rw [div_pow]
  field_simp

/-- A fixed finite diagonal listing misses a linear row margin with at most the corrected
KL-Chernoff union bound. -/
theorem linear_margin_bound [Fintype A] [Fintype Y] (f : Y → Y) (alpha : ℝ)
    (hA : 2 ≤ Fintype.card A) (hY : 2 ≤ Fintype.card Y) (halpha : 0 < alpha)
    (hqp : alpha * (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) - 1) <
      ((Fintype.card Y : ℝ) - 1) / (Fintype.card Y : ℝ)) :
    marginFailureProbability (A := A) f alpha ≤
      (Fintype.card A : ℝ) *
        Real.exp (-((Fintype.card A : ℝ) - 1) *
          bernoulliKL
            (alpha * (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) - 1))
            (((Fintype.card Y : ℝ) - 1) / (Fintype.card Y : ℝ))) := by
  classical
  let m := Fintype.card A
  let y := Fintype.card Y
  let r := m - 1
  let t := alpha * (m : ℝ)
  let q := alpha * (m : ℝ) / ((m : ℝ) - 1)
  let p := ((y : ℝ) - 1) / (y : ℝ)
  let s := Nat.ceil t
  let tail := ∑ j ∈ Finset.Icc s m, rowDistanceCount (A := A) f j
  let bad := ∑ j ∈ Finset.range s, rowDistanceCount (A := A) f j
  let total := y ^ m
  let pref := binomialPrefixCount r (y - 1) s
  let x := (tail : ℝ) / total
  have hA1 : 1 ≤ m := by omega
  have hY1 : 1 ≤ y := by omega
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast Nat.zero_lt_of_lt hA1
  have hy_pos : (0 : ℝ) < y := by exact_mod_cast Nat.zero_lt_of_lt hY1
  have hr_nat : 1 ≤ r := by omega
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast Nat.zero_lt_of_lt hr_nat
  have hr_cast : (r : ℝ) = (m : ℝ) - 1 := by
    dsimp [r]
    rw [Nat.cast_sub hA1, Nat.cast_one]
  have hp_pos : 0 < p := by
    have hy_one : (1 : ℝ) < y := by exact_mod_cast hY
    dsimp [p]
    exact div_pos (sub_pos.mpr hy_one) hy_pos
  have hp_one : p < 1 := by
    dsimp [p]
    rw [div_lt_one hy_pos]
    linarith
  have hq_pos : 0 < q := by
    dsimp [q]
    exact div_pos (mul_pos halpha hm_pos) (by linarith)
  have hqp' : q < p := by exact hqp
  have hq_one : q < 1 := hqp'.trans hp_one
  have ht_qr : t = q * (r : ℝ) := by
    dsimp [t, q]
    rw [hr_cast]
    field_simp [show (m : ℝ) - 1 ≠ 0 by linarith]
  have ht_lt_r : t < (r : ℝ) := by
    rw [ht_qr]
    simpa only [one_mul] using mul_lt_mul_of_pos_right hq_one hr_pos
  have hs_r : s ≤ r := by
    dsimp [s]
    exact Nat.ceil_le.mpr ht_lt_r.le
  have hs_m : s ≤ m + 1 := by omega
  have hsplit : tail + bad = total := by
    exact row_tail_add_prefix f s hA1 hY1 hs_m
  have htail : tail ≤ total := by omega
  have htotal_pos : 0 < total := by
    dsimp [total]
    positivity
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hprob : marginFailureProbability (A := A) f alpha = 1 - x ^ m := by
    simpa only [m, y, t, s, tail, total, x, Nat.cast_pow] using
      marginFailureProbability_eq_one_sub_pow f alpha hA1 hY1 hs_m
  have hbernoulli := one_add_mul_sub_le_pow (a := x) (by linarith : -1 ≤ x) m
  have hunion : 1 - x ^ m ≤ (m : ℝ) * (1 - x) := by
    linarith
  have hrow : bad ≤ y * pref := by
    exact row_prefix_le_binomial f s
  have hsplit_cast : (tail : ℝ) + bad = total := by exact_mod_cast hsplit
  have hone_sub : 1 - x = (bad : ℝ) / total := by
    dsimp [x]
    field_simp
    linarith
  have hrow_ratio : 1 - x ≤ (pref : ℝ) / (y : ℝ) ^ r := by
    rw [hone_sub]
    calc
      (bad : ℝ) / total ≤ ((y * pref : ℕ) : ℝ) / total := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hrow) (Nat.cast_nonneg total)
      _ = (pref : ℝ) / (y : ℝ) ^ r := by
        dsimp [total]
        simp only [Nat.cast_mul, Nat.cast_pow]
        have hm : m = r + 1 := by omega
        rw [hm, pow_succ]
        field_simp
  have hprefix_kl : (pref : ℝ) / (y : ℝ) ^ r ≤
      Real.exp (-(r : ℝ) * bernoulliKL q p) := by
    calc
      (pref : ℝ) / (y : ℝ) ^ r =
          Bin(ℝ, r, binomialParameter y hY1).real {z | z < t} := by
        dsimp [pref, s]
        exact binomial_prefix_ratio r y t hY1 (by omega)
      _ ≤ Bin(ℝ, r, binomialParameter y hY1).real {z | z ≤ q * (r : ℝ)} := by
        refine measureReal_mono ?_ (by finiteness)
        intro z hz
        change z < t at hz
        change z ≤ q * (r : ℝ)
        rw [← ht_qr]
        exact hz.le
      _ ≤ Real.exp (-(r : ℝ) * bernoulliKL q p) := by
        simpa only [binomialParameter, p] using
          binomial_lower_tail_kl r (binomialParameter y hY1) hq_pos hqp' hp_one
  calc
    marginFailureProbability (A := A) f alpha = 1 - x ^ m := hprob
    _ ≤ (m : ℝ) * (1 - x) := hunion
    _ ≤ (m : ℝ) * ((pref : ℝ) / (y : ℝ) ^ r) := by gcongr
    _ ≤ (m : ℝ) * Real.exp (-(r : ℝ) * bernoulliKL q p) := by gcongr
    _ = (Fintype.card A : ℝ) *
        Real.exp (-((Fintype.card A : ℝ) - 1) *
          bernoulliKL
            (alpha * (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) - 1))
            (((Fintype.card Y : ℝ) - 1) / (Fintype.card Y : ℝ))) := by
      simp only [m, y, q, p, hr_cast]

end D5.S0.Diagonal.MarginBound
