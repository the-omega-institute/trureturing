/- GID: D5/S0/Diagonal/TypicalDensity
   generality: G
   mirror-B: D5/B/S0/Diagonal/TypicalDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two-sided concentration of the minimum diagonal-distance density. -/

import D5.S0.Diagonal.MarginVanishing

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory unitInterval

universe u v

namespace D5.S0.Diagonal.TypicalDensity

open DistanceProfile MarginBound MarginVanishing

variable {A : Type u} {Y : Type v}

/-- The single-row factor for distances strictly above `alpha * |A|`. -/
noncomputable def rowUpperProbability [Fintype A] [Fintype Y]
    (f : Y → Y) (alpha : ℝ) : ℝ :=
  ((∑ j ∈ Finset.Icc (Nat.floor (alpha * Fintype.card A) + 1) (Fintype.card A),
      rowDistanceCount (A := A) f j : ℕ) : ℝ) /
    (Fintype.card Y : ℝ) ^ Fintype.card A

/-- The uniform probability that every row distance is strictly above `alpha * |A|`. -/
noncomputable def upperFailureProbability [Fintype A] [Fintype Y]
    (f : Y → Y) (alpha : ℝ) : ℝ :=
  Nat.card {g : A → A → Y //
      ∀ a, Nat.floor (alpha * Fintype.card A) + 1 ≤ hammingDistance f g a} /
    Nat.card (A → A → Y)

/-- The uniform probability that the minimum row distance lies outside the prescribed interval. -/
noncomputable def typicalDensityFailureProbability [Fintype A] [Fintype Y]
    (f : Y → Y) (alphaLo alphaHi : ℝ) : ℝ :=
  Nat.card {g : A → A → Y //
      (∃ a, (hammingDistance f g a : ℝ) < alphaLo * Fintype.card A) ∨
        ∀ a, Nat.floor (alphaHi * Fintype.card A) + 1 ≤ hammingDistance f g a} /
    Nat.card (A → A → Y)

/-- The KL-Chernoff upper tail for a binomial random variable. -/
theorem binomial_upper_tail_kl (r : ℕ) {q : ℝ} (p : Set.Icc (0 : ℝ) 1)
    (hp : 0 < (p : ℝ)) (hpq : (p : ℝ) < q) (hq_one : q < 1) :
    Bin(ℝ, r, p).real {x | q * r ≤ x} ≤
      Real.exp (-(r : ℝ) * bernoulliKL q p) := by
  have hq : 0 < q := hp.trans hpq
  have hp_one : (p : ℝ) < 1 := hpq.trans hq_one
  have hqc : 0 < 1 - q := sub_pos.mpr hq_one
  have hpc : 0 < 1 - (p : ℝ) := sub_pos.mpr hp_one
  let t := Real.log (q * (1 - (p : ℝ)) / ((p : ℝ) * (1 - q)))
  have hratio_pos : 0 < q * (1 - (p : ℝ)) / ((p : ℝ) * (1 - q)) := by
    positivity
  have hratio_ge : 1 ≤ q * (1 - (p : ℝ)) / ((p : ℝ) * (1 - q)) := by
    rw [one_le_div (mul_pos hp hqc)]
    nlinarith
  have ht : 0 ≤ t := Real.log_nonneg hratio_ge
  have h_int : Integrable (fun x : ℝ => Real.exp (t * id x)) Bin(ℝ, r, p) :=
    integrable_map_cast_binomial _
  have hchernoff := measure_ge_le_exp_mul_mgf
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
    Bin(ℝ, r, p).real {x | q * r ≤ x} ≤
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

/-- The upper deviation of the minimum is bounded by its exact single-row factor. -/
theorem upper_failure_probability_le_row_probability [Fintype A] [Fintype Y]
    (f : Y → Y) (alpha : ℝ) (hA : 1 ≤ Fintype.card A) (hY : 1 ≤ Fintype.card Y) :
    upperFailureProbability (A := A) f alpha ≤ rowUpperProbability (A := A) f alpha := by
  classical
  let m := Fintype.card A
  let y := Fintype.card Y
  let s := Nat.floor (alpha * (m : ℝ)) + 1
  let tail := ∑ j ∈ Finset.Icc s m, rowDistanceCount (A := A) f j
  let total := y ^ m
  let x := (tail : ℝ) / total
  have hrowTotal :
      (∑ j ∈ Finset.Icc 0 m, rowDistanceCount (A := A) f j) = total := by
    have hpow :
        (∑ j ∈ Finset.Icc 0 m, rowDistanceCount (A := A) f j) ^ m = total ^ m := by
      dsimp [m, total]
      rw [← min_distance_tail]
      let e : {g : A → A → Y // ∀ a, 0 ≤ hammingDistance f g a} ≃
          (A → A → Y) :=
        { toFun := Subtype.val
          invFun := fun g => ⟨g, fun _ => Nat.zero_le _⟩
          left_inv := by intro g; exact Subtype.ext rfl
          right_inv := by intro g; rfl }
      rw [Nat.card_congr e]
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun]
    exact Nat.pow_left_injective (by omega : m ≠ 0) hpow
  have htail : tail ≤ total := by
    rw [← hrowTotal]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro j hj; exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hj).2⟩)
      (by intro _ _ _; positivity)
  have htotal_pos : (0 : ℝ) < total := by
    dsimp [total]
    positivity
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx_one : x ≤ 1 := by
    dsimp [x]
    rw [div_le_one htotal_pos]
    exact_mod_cast htail
  have hprob : upperFailureProbability (A := A) f alpha = x ^ m := by
    rw [upperFailureProbability, min_distance_tail]
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun]
    change ((tail ^ m : ℕ) : ℝ) / (((total ^ m : ℕ) : ℝ)) = x ^ m
    simp only [Nat.cast_pow]
    exact (div_pow (tail : ℝ) (total : ℝ) m).symm
  have hpowSelf : x ^ m ≤ x := by
    obtain ⟨n, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    rw [hm, pow_succ']
    calc
      x * x ^ n ≤ x * 1 := by gcongr; exact pow_le_one₀ hx_nonneg hx_one
      _ = x := mul_one x
  calc
    upperFailureProbability (A := A) f alpha = x ^ m := hprob
    _ ≤ x := hpowSelf
    _ = rowUpperProbability (A := A) f alpha := by
      simp only [rowUpperProbability, x, tail, total, s, m, y, Nat.cast_pow]

private def binomialSuffixCount (r c s : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc s r, r.choose k * c ^ k

private noncomputable def upperBinomialParameter (y : ℕ) (hy : 1 ≤ y) :
    Set.Icc (0 : ℝ) 1 :=
  ⟨((y : ℝ) - 1) / y, by
    constructor
    · exact div_nonneg (by exact_mod_cast Nat.zero_le (y - 1)) (Nat.cast_nonneg y)
    · rw [div_le_one (by exact_mod_cast Nat.zero_lt_of_lt hy)]
      linarith⟩

private theorem binomial_suffix_shift (r c s : ℕ) :
    (∑ j ∈ Finset.Icc (s + 1) (r + 1), r.choose (j - 1) * c ^ (j - 1)) =
      binomialSuffixCount r c s := by
  symm
  apply Finset.sum_bij (fun k _ => k + 1)
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro k₁ hk₁ k₂ hk₂ h
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨j - 1, ?_, by omega⟩
    simp only [Finset.mem_Icc]
    omega
  · intro k hk
    simp

private theorem first_binomial_suffix_le (r c s : ℕ) (hs : s ≤ r) :
    (∑ j ∈ Finset.Icc (s + 1) (r + 1), r.choose j * c ^ j) ≤
      binomialSuffixCount r c s := by
  calc
    (∑ j ∈ Finset.Icc (s + 1) (r + 1), r.choose j * c ^ j) =
        ∑ j ∈ Finset.Icc (s + 1) r, r.choose j * c ^ j := by
      rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega)]
      simp [Nat.choose_eq_zero_of_lt]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro j hj
        rcases Finset.mem_Icc.mp hj with ⟨hlo, hhi⟩
        exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩)
      (by intro _ _ _; positivity)

private theorem row_upper_count_le_binomial [Fintype A] [Fintype Y]
    (f : Y → Y) (s : ℕ) (hA : 1 ≤ Fintype.card A)
    (hs : s ≤ Fintype.card A - 1) :
    (∑ j ∈ Finset.Icc (s + 1) (Fintype.card A), rowDistanceCount (A := A) f j) ≤
      Fintype.card Y *
        binomialSuffixCount (Fintype.card A - 1) (Fintype.card Y - 1) s := by
  classical
  let m := Fintype.card A
  let y := Fintype.card Y
  let r := m - 1
  let c := y - 1
  let fixed := Nat.card {z : Y // f z = z}
  have hm : m = r + 1 := by omega
  have hfixed : fixed ≤ y := by
    dsimp [fixed, y]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  have hfirst := first_binomial_suffix_le r c s (by simpa only [r, m] using hs)
  have hsecond := binomial_suffix_shift r c s
  change (∑ j ∈ Finset.Icc (s + 1) m, rowDistanceCount (A := A) f j) ≤
    y * binomialSuffixCount r c s
  rw [hm]
  rw [show (∑ j ∈ Finset.Icc (s + 1) (r + 1), rowDistanceCount (A := A) f j) =
      ∑ j ∈ Finset.Icc (s + 1) (r + 1),
        (fixed * (r.choose j * c ^ j) +
          (y - fixed) * (r.choose (j - 1) * c ^ (j - 1))) by
    apply Finset.sum_congr rfl
    intro j hj
    have hj0 : j ≠ 0 := by
      rcases Finset.mem_Icc.mp hj with ⟨hlo, _⟩
      omega
    rw [rowDistanceCount, if_neg hj0]
    simp only [m, y, r, c, fixed]
    ring]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsecond]
  calc
    fixed * (∑ j ∈ Finset.Icc (s + 1) (r + 1), r.choose j * c ^ j) +
        (y - fixed) * binomialSuffixCount r c s ≤
      fixed * binomialSuffixCount r c s +
        (y - fixed) * binomialSuffixCount r c s := by gcongr
    _ = y * binomialSuffixCount r c s := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hfixed]

private theorem binomial_suffix_ratio (r y s : ℕ) (hy : 1 ≤ y) :
    (binomialSuffixCount r (y - 1) s : ℝ) / (y : ℝ) ^ r =
      Bin(ℝ, r, upperBinomialParameter y hy).real {x | (s : ℝ) ≤ x} := by
  classical
  have hy_pos : (0 : ℝ) < y := by exact_mod_cast Nat.zero_lt_of_lt hy
  have hp_compl : 1 - (upperBinomialParameter y hy : ℝ) = 1 / (y : ℝ) := by
    change 1 - ((y : ℝ) - 1) / y = 1 / y
    field_simp
    ring
  have hsubset : Finset.Icc s r ⊆ Finset.Iic r := by
    intro k hk
    exact Finset.mem_Iic.mpr (Finset.mem_Icc.mp hk).2
  have hmeasure :
      Bin(ℝ, r, upperBinomialParameter y hy).real {x | (s : ℝ) ≤ x} =
        ∑ k ∈ Finset.Icc s r,
          (r.choose k : ℝ) * (upperBinomialParameter y hy : ℝ) ^ k *
            (1 - (upperBinomialParameter y hy : ℝ)) ^ (r - k) := by
    calc
      Bin(ℝ, r, upperBinomialParameter y hy).real {x | (s : ℝ) ≤ x} =
          ∫ x, {x : ℝ | (s : ℝ) ≤ x}.indicator 1 x
            ∂Bin(ℝ, r, upperBinomialParameter y hy) := by
        rw [integral_indicator_one]
        exact measurableSet_le measurable_const measurable_id
      _ = ∑ k ∈ Finset.Iic r,
          ((r.choose k : ℝ) * (upperBinomialParameter y hy : ℝ) ^ k *
            (1 - (upperBinomialParameter y hy : ℝ)) ^ (r - k)) •
              {x : ℝ | (s : ℝ) ≤ x}.indicator 1 (k : ℝ) :=
        integral_map_cast_binomial _
      _ = ∑ k ∈ Finset.Icc s r,
          ((r.choose k : ℝ) * (upperBinomialParameter y hy : ℝ) ^ k *
            (1 - (upperBinomialParameter y hy : ℝ)) ^ (r - k)) •
              {x : ℝ | (s : ℝ) ≤ x}.indicator 1 (k : ℝ) := by
        symm
        apply Finset.sum_subset hsubset
        intro k hkr hk
        have hks : k < s := by
          have hkr' := Finset.mem_Iic.mp hkr
          have hk' : ¬(s ≤ k ∧ k ≤ r) := by simpa only [Finset.mem_Icc] using hk
          omega
        rw [Set.indicator_of_notMem]
        · simp
        · simpa only [Set.mem_setOf_eq, Nat.cast_le] using not_le_of_gt hks
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkmem : (k : ℝ) ∈ {x : ℝ | (s : ℝ) ≤ x} := by
          simpa only [Set.mem_setOf_eq, Nat.cast_le] using (Finset.mem_Icc.mp hk).1
        rw [Set.indicator_of_mem hkmem]
        simp
  rw [hmeasure, binomialSuffixCount, Nat.cast_sum, Finset.sum_div]
  simp only [Nat.cast_mul, Nat.cast_pow]
  apply Finset.sum_congr rfl
  intro k hk
  have hkr : k ≤ r := (Finset.mem_Icc.mp hk).2
  rw [Nat.cast_sub hy, hp_compl]
  simp only [upperBinomialParameter, Nat.cast_one]
  change (r.choose k : ℝ) * ((y : ℝ) - 1) ^ k / (y : ℝ) ^ r =
    (r.choose k : ℝ) * (((y : ℝ) - 1) / y) ^ k * (1 / (y : ℝ)) ^ (r - k)
  rw [div_pow, one_div, inv_pow]
  field_simp
  rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hkr]

private theorem row_upper_probability_le_exp [Fintype A] [Fintype Y]
    (f : Y → Y) (alpha : ℝ) (hA : 2 ≤ Fintype.card A) (hY : 2 ≤ Fintype.card Y)
    (hpq : ((Fintype.card Y : ℝ) - 1) / Fintype.card Y <
      (alpha * Fintype.card A - 1) / ((Fintype.card A : ℝ) - 1))
    (halpha_one : alpha < 1) :
    rowUpperProbability (A := A) f alpha ≤
      Real.exp (-((Fintype.card A : ℝ) - 1) *
        bernoulliKL
          ((alpha * Fintype.card A - 1) / ((Fintype.card A : ℝ) - 1))
          (((Fintype.card Y : ℝ) - 1) / Fintype.card Y)) := by
  classical
  let m := Fintype.card A
  let y := Fintype.card Y
  let r := m - 1
  let s := Nat.floor (alpha * (m : ℝ))
  let p := ((y : ℝ) - 1) / (y : ℝ)
  let q := (alpha * (m : ℝ) - 1) / ((m : ℝ) - 1)
  let param := upperBinomialParameter y (by omega : 1 ≤ y)
  have hm_pos : (0 : ℝ) < m := by positivity
  have hy_pos : (0 : ℝ) < y := by positivity
  have hr_nat : 1 ≤ r := by omega
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast Nat.zero_lt_of_lt hr_nat
  have hr_cast : (r : ℝ) = (m : ℝ) - 1 := by
    dsimp [r]
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  have hp_pos : 0 < p := by
    dsimp [p]
    have hy_one : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
    exact div_pos (sub_pos.mpr hy_one) hy_pos
  have hq_pos : 0 < q := hp_pos.trans (by exact hpq)
  have halpha_pos : 0 < alpha := by
    have hnum : 0 < alpha * (m : ℝ) - 1 := by
      dsimp [q] at hq_pos
      rcases div_pos_iff.mp hq_pos with h | h
      · exact h.1
      · linarith
    nlinarith
  have hq_one : q < 1 := by
    dsimp [q]
    rw [div_lt_one (by linarith : 0 < (m : ℝ) - 1)]
    nlinarith
  have hs : s ≤ r := by
    have hnonneg : 0 ≤ alpha * (m : ℝ) := (mul_pos halpha_pos hm_pos).le
    have hlt : alpha * (m : ℝ) < m := by
      nlinarith [mul_lt_mul_of_pos_right halpha_one hm_pos]
    have := (Nat.floor_lt hnonneg).mpr hlt
    dsimp [s, r]
    omega
  have hcount :
      (∑ j ∈ Finset.Icc (s + 1) m, rowDistanceCount (A := A) f j) ≤
        y * binomialSuffixCount r (y - 1) s := by
    simpa only [m, y, r] using
      row_upper_count_le_binomial (A := A) f s (by omega) hs
  have hrow : rowUpperProbability (A := A) f alpha ≤
      (binomialSuffixCount r (y - 1) s : ℝ) / (y : ℝ) ^ r := by
    rw [rowUpperProbability]
    change (↑(∑ j ∈ Finset.Icc (s + 1) m, rowDistanceCount (A := A) f j) : ℝ) /
        (y : ℝ) ^ m ≤ (binomialSuffixCount r (y - 1) s : ℝ) / (y : ℝ) ^ r
    calc
      (↑(∑ j ∈ Finset.Icc (s + 1) m, rowDistanceCount (A := A) f j) : ℝ) /
          (y : ℝ) ^ m ≤
        (↑(y * binomialSuffixCount r (y - 1) s) : ℝ) / (y : ℝ) ^ m := by
          gcongr
      _ = (binomialSuffixCount r (y - 1) s : ℝ) / (y : ℝ) ^ r := by
        rw [show m = r + 1 by omega, pow_succ]
        simp only [Nat.cast_mul]
        field_simp
  have hratio : (binomialSuffixCount r (y - 1) s : ℝ) / (y : ℝ) ^ r =
      Bin(ℝ, r, param).real {x | (s : ℝ) ≤ x} := by
    simpa only [param] using binomial_suffix_ratio r y s (by omega)
  have hqr : q * (r : ℝ) = alpha * (m : ℝ) - 1 := by
    dsimp [q]
    rw [hr_cast]
    field_simp [show (m : ℝ) - 1 ≠ 0 by linarith]
  have hqs : q * (r : ℝ) ≤ (s : ℝ) := by
    rw [hqr]
    have hfloor := Nat.lt_floor_add_one (alpha * (m : ℝ))
    dsimp [s]
    linarith
  have hmeasure : Bin(ℝ, r, param).real {x | (s : ℝ) ≤ x} ≤
      Bin(ℝ, r, param).real {x | q * (r : ℝ) ≤ x} := by
    refine measureReal_mono ?_ (by finiteness)
    intro x hx
    exact hqs.trans hx
  calc
    rowUpperProbability (A := A) f alpha ≤
        (binomialSuffixCount r (y - 1) s : ℝ) / (y : ℝ) ^ r := hrow
    _ = Bin(ℝ, r, param).real {x | (s : ℝ) ≤ x} := hratio
    _ ≤ Bin(ℝ, r, param).real {x | q * (r : ℝ) ≤ x} := hmeasure
    _ ≤ Real.exp (-(r : ℝ) * bernoulliKL q p) := by
      simpa only [param, upperBinomialParameter, p] using
        binomial_upper_tail_kl r param hp_pos (by exact hpq) hq_one
    _ = _ := by
      simp only [m, y, q, p, hr_cast]

private theorem tendsto_adjusted_upper (alpha : ℝ) :
    Tendsto (fun a : ℕ => (alpha * (a : ℝ) - 1) / ((a : ℝ) - 1))
      atTop (nhds alpha) := by
  have hden : Tendsto (fun a : ℕ => (a : ℝ) - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun a : ℕ => ((a : ℝ) - 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hlim : Tendsto (fun a : ℕ => alpha + (alpha - 1) * ((a : ℝ) - 1)⁻¹)
      atTop (nhds alpha) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 1] with a ha
  have hden_ne : (a : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < a := by exact_mod_cast ha
    linarith
  field_simp
  ring

/-- Above the nonzero-choice density, the upper-deviation probability vanishes. -/
theorem upper_failure_probability_tendsto_zero {Y : Type u} [Fintype Y] (f : Y → Y)
    (alpha : ℝ) (hY : 2 ≤ Fintype.card Y)
    (halpha_gt : ((Fintype.card Y : ℝ) - 1) / Fintype.card Y < alpha)
    (halpha_one : alpha < 1) :
    Tendsto (fun a : ℕ => upperFailureProbability (A := Fin a) f alpha)
      atTop (nhds 0) := by
  let p := ((Fintype.card Y : ℝ) - 1) / Fintype.card Y
  let c := bernoulliKL alpha p
  let b := c / 2
  have hy_pos : (0 : ℝ) < Fintype.card Y := by positivity
  have hy_one : (1 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  have hp_pos : 0 < p := by
    dsimp [p]
    exact div_pos (sub_pos.mpr hy_one) hy_pos
  have hp_one : p < 1 := by
    dsimp [p]
    rw [div_lt_one hy_pos]
    linarith
  have halpha_pos : 0 < alpha := hp_pos.trans halpha_gt
  have hc_pos : 0 < c := by
    exact bernoulliKL_pos halpha_pos halpha_one hp_pos hp_one (ne_of_gt halpha_gt)
  have hb_pos : 0 < b := by positivity
  have hq := tendsto_adjusted_upper alpha
  have hkl : Tendsto
      (fun a : ℕ => bernoulliKL
        ((alpha * (a : ℝ) - 1) / ((a : ℝ) - 1)) p)
      atTop (nhds c) := by
    exact (continuousAt_bernoulliKL halpha_pos halpha_one hp_pos hp_one).tendsto.comp
      (hq.prodMk_nhds tendsto_const_nhds)
  have hmodel : Tendsto
      (fun a : ℕ => Real.exp b * Real.exp (-b * (a : ℝ)))
      atTop (nhds 0) := by
    have hbase := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb_pos).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply, Real.rpow_zero, one_mul, mul_zero] using
      tendsto_const_nhds.mul hbase
  apply squeeze_zero'
  · exact Eventually.of_forall fun a => by
      unfold upperFailureProbability
      positivity
  · filter_upwards [eventually_gt_atTop 1, hq.eventually_const_lt halpha_gt,
      hkl.eventually_const_lt (by dsimp [b]; linarith : b < c)] with a ha hqa hrate
    have ha_two : 2 ≤ a := by omega
    have ha_real : (1 : ℝ) < a := by exact_mod_cast ha
    have hexponent :
        -((a : ℝ) - 1) *
            bernoulliKL ((alpha * (a : ℝ) - 1) / ((a : ℝ) - 1)) p ≤
          b - b * (a : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hrate.le (sub_nonneg.mpr ha_real.le)]
    calc
      upperFailureProbability (A := Fin a) f alpha ≤
          rowUpperProbability (A := Fin a) f alpha :=
        upper_failure_probability_le_row_probability f alpha
          (by simpa only [Fintype.card_fin] using ha.le) (by omega)
      _ ≤ Real.exp (-((a : ℝ) - 1) *
          bernoulliKL ((alpha * (a : ℝ) - 1) / ((a : ℝ) - 1)) p) := by
        simpa only [Fintype.card_fin, p] using
          row_upper_probability_le_exp (A := Fin a) f alpha
            (by simpa only [Fintype.card_fin] using ha_two) hY
            (by simpa only [Fintype.card_fin, p] using hqa) halpha_one
      _ ≤ Real.exp (b - b * (a : ℝ)) := by gcongr
      _ = Real.exp b * Real.exp (-b * (a : ℝ)) := by
        rw [show b - b * (a : ℝ) = b + (-b * (a : ℝ)) by ring, Real.exp_add]
  · exact hmodel

/-- For fixed densities on either side of the nonzero-choice density, the minimum row-distance
density lies in the closed interval between them with probability tending to one. -/
theorem typical_density_failure_probability_tendsto_zero {Y : Type u} [Fintype Y]
    (f : Y → Y) (alphaLo alphaHi : ℝ) (hY : 2 ≤ Fintype.card Y)
    (halphaLo : 0 < alphaLo)
    (halphaLo_lt : alphaLo < ((Fintype.card Y : ℝ) - 1) / Fintype.card Y)
    (halphaHi_gt : ((Fintype.card Y : ℝ) - 1) / Fintype.card Y < alphaHi)
    (halphaHi_one : alphaHi < 1) :
    Tendsto
      (fun a : ℕ => typicalDensityFailureProbability (A := Fin a) f alphaLo alphaHi)
      atTop (nhds 0) := by
  have hlower := margin_failure_probability_tendsto_zero f alphaLo hY halphaLo halphaLo_lt
  have hupper :=
    upper_failure_probability_tendsto_zero f alphaHi hY halphaHi_gt halphaHi_one
  apply squeeze_zero' (g := fun a : ℕ =>
    marginFailureProbability (A := Fin a) f alphaLo +
      upperFailureProbability (A := Fin a) f alphaHi)
  · exact Eventually.of_forall fun a => by
      unfold typicalDensityFailureProbability
      positivity
  · exact Eventually.of_forall fun a => by
      classical
      let lower : (Fin a → Fin a → Y) → Prop := fun g =>
        ∃ x, (hammingDistance f g x : ℝ) < alphaLo * Fintype.card (Fin a)
      let upper : (Fin a → Fin a → Y) → Prop := fun g =>
        ∀ x, Nat.floor (alphaHi * Fintype.card (Fin a)) + 1 ≤ hammingDistance f g x
      have hcard : Nat.card {g : Fin a → Fin a → Y // lower g ∨ upper g} ≤
          Nat.card {g : Fin a → Fin a → Y // lower g} +
            Nat.card {g : Fin a → Fin a → Y // upper g} := by
        simp only [Nat.card_eq_fintype_card]
        exact Fintype.card_subtype_or lower upper
      rw [typicalDensityFailureProbability, marginFailureProbability,
        upperFailureProbability]
      change (Nat.card {g : Fin a → Fin a → Y // lower g ∨ upper g} : ℝ) /
          Nat.card (Fin a → Fin a → Y) ≤
        (Nat.card {g : Fin a → Fin a → Y // lower g} : ℝ) /
            Nat.card (Fin a → Fin a → Y) +
          (Nat.card {g : Fin a → Fin a → Y // upper g} : ℝ) /
            Nat.card (Fin a → Fin a → Y)
      rw [← add_div]
      gcongr
      exact_mod_cast hcard
  · simpa only [add_zero] using hlower.add hupper

end D5.S0.Diagonal.TypicalDensity
