/- GID: D5/S1/Digit/DigitCapPlateau
   generality: I
   mirror-B: D5/B/S1/Digit/DigitCapPlateau
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: On each plateau of digit caps the count at (q-1) times a repunit is q^m and the exponent is log q over log ell. -/

import D5.S1.Digit.DigitCapQuotientBound

/-! # Plateaus of the bounded-digit upper growth exponent

For a radix `ell ≥ 2`, an integer `2 ≤ q ≤ ell` and a digit cap `k` with
`(q - 1) * (ell + 1) ≤ k ≤ q * ell - 1`, the input `(q - 1) * (1 + ell + ... + ell ^ m)`
has exactly `q ^ m` bounded-digit representations, and the upper logarithmic growth exponent
equals `log q / log ell`.
-/

namespace D5.S1.Digit.DigitCapPlateau

open D5.S1.Digit.CoonsAdjacentGrowthRefutation
open D5.S1.Digit.DigitCapQuotientBound
open scoped BigOperators

noncomputable section

/-- The repunit `1 + ell + ... + ell ^ m` in radix `ell`. -/
def repunitSum (ell m : ℕ) : ℕ := ∑ i ∈ Finset.range (m + 1), ell ^ i

private def window (ell m : ℕ) (u : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, u i * ell ^ i

private lemma window_succ (ell m : ℕ) (u : ℕ → ℕ) :
    window ell (m + 1) u = u 0 + ell * window ell m (fun i => u (i + 1)) := by
  simp only [window, Finset.sum_range_succ', pow_zero, mul_one, pow_succ,
    Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private def pack (m : ℕ) (u : ℕ → ℕ) : ℕ →₀ ℕ :=
  Finsupp.onFinset (Finset.range m) (fun i => if i < m then u i else 0)
    (by intro i hi; simp only [Finset.mem_range]; by_contra h; simp [h] at hi)

private lemma pack_apply (m : ℕ) (u : ℕ → ℕ) (i : ℕ) :
    pack m u i = if i < m then u i else 0 := rfl

private lemma weight_pack (ell m : ℕ) (u : ℕ → ℕ) :
    weight ell (pack m u) = window ell m u := by
  unfold weight window
  rw [Finsupp.sum_of_support_subset (s := Finset.range m)]
  · apply Finset.sum_congr rfl
    intro i hi
    simp [pack_apply, Finset.mem_range.mp hi]
  · intro i hi
    simp only [Finset.mem_range]
    by_contra hn
    exact Finsupp.mem_support_iff.mp hi (by simp [pack_apply, hn])
  · simp

private lemma repunit_top (ell m : ℕ) (hell : 1 ≤ ell) :
    (ell - 1) * repunitSum ell m + 1 = ell ^ (m + 1) := by
  induction m with
  | zero => simp [repunitSum]; omega
  | succ m ih =>
    have hr : repunitSum ell (m + 1) = repunitSum ell m + ell ^ (m + 1) := by
      simp [repunitSum, Finset.sum_range_succ]
    rw [hr, Nat.mul_add, pow_succ ell (m + 1)]
    have h1 : (ell - 1) * ell ^ (m + 1) + ell ^ (m + 1) = ell ^ (m + 1) * ell := by
      have : ell - 1 + 1 = ell := Nat.sub_add_cancel hell
      calc (ell - 1) * ell ^ (m + 1) + ell ^ (m + 1)
          = (ell - 1 + 1) * ell ^ (m + 1) := by ring
        _ = ell ^ (m + 1) * ell := by rw [this, Nat.mul_comm]
    omega

private lemma pow_le_repunit (ell m : ℕ) : ell ^ m ≤ repunitSum ell m := by
  unfold repunitSum
  exact Finset.single_le_sum (f := fun i => ell ^ i) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_self m))

private def carries {q m : ℕ} (v : Fin m → Fin q) (i : ℕ) : ℕ :=
  if hi : 0 < i ∧ i ≤ m then (v ⟨i - 1, by omega⟩).val else 0

private lemma carries_le {q m : ℕ} (hq : 1 ≤ q) (v : Fin m → Fin q) (i : ℕ) :
    carries v i ≤ q - 1 := by
  unfold carries
  split_ifs with h
  · have := (v ⟨i - 1, by omega⟩).isLt
    omega
  · omega

private lemma carries_zero {q m : ℕ} (v : Fin m → Fin q) : carries v 0 = 0 := by
  simp [carries]

private lemma carries_end {q m : ℕ} (v : Fin m → Fin q) : carries v (m + 1) = 0 := by
  simp [carries]

private def carryDigit {q m : ℕ} (ell : ℕ) (v : Fin m → Fin q) (i : ℕ) : ℕ :=
  (q - 1) + ell * carries v (i + 1) - carries v i

private lemma carry_digit_balance {q m : ℕ} (ell : ℕ) (hq : 1 ≤ q) (v : Fin m → Fin q)
    (i : ℕ) : carryDigit ell v i + carries v i = (q - 1) + ell * carries v (i + 1) := by
  have := carries_le hq v i
  unfold carryDigit
  omega

private lemma carry_digit_le {q m : ℕ} (ell : ℕ) (hq : 1 ≤ q) (v : Fin m → Fin q)
    (i : ℕ) : carryDigit ell v i ≤ (q - 1) * (ell + 1) := by
  have h := carries_le hq v (i + 1)
  have h2 : ell * carries v (i + 1) ≤ ell * (q - 1) := Nat.mul_le_mul_left ell h
  unfold carryDigit
  have h3 : (q - 1) * (ell + 1) = (q - 1) + ell * (q - 1) := by ring
  omega

private lemma carry_weight {q m : ℕ} (ell : ℕ) (hq : 1 ≤ q) (v : Fin m → Fin q) :
    weight ell (pack (m + 1) (carryDigit ell v)) = (q - 1) * repunitSum ell m := by
  rw [weight_pack]
  have hbal : window ell (m + 1) (carryDigit ell v) + window ell (m + 1) (carries v) =
      (q - 1) * repunitSum ell m + ell * window ell (m + 1) (fun i => carries v (i + 1)) := by
    simp only [window, repunitSum, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := carry_digit_balance ell hq v i
    calc carryDigit ell v i * ell ^ i + carries v i * ell ^ i
        = (carryDigit ell v i + carries v i) * ell ^ i := by ring
      _ = ((q - 1) + ell * carries v (i + 1)) * ell ^ i := by rw [h]
      _ = (q - 1) * ell ^ i + ell * (carries v (i + 1) * ell ^ i) := by ring
  have htail : window ell (m + 1) (fun i => carries v (i + 1)) =
      window ell m (fun i => carries v (i + 1)) := by
    simp [window, Finset.sum_range_succ, carries_end]
  rw [window_succ ell m (carries v), carries_zero, zero_add, htail] at hbal
  omega

private def carryPartition (ell q k m : ℕ) (hq : 1 ≤ q) (hk : (q - 1) * (ell + 1) ≤ k)
    (v : Fin m → Fin q) : Partitions k ell ((q - 1) * repunitSum ell m) :=
  ⟨pack (m + 1) (carryDigit ell v), (by
    intro i
    rw [pack_apply]
    split_ifs
    · exact (carry_digit_le ell hq v i).trans hk
    · omega), carry_weight ell hq v⟩

private lemma carry_partition_injective (ell q k m : ℕ) (hell : 1 ≤ ell) (hq : 1 ≤ q)
    (hk : (q - 1) * (ell + 1) ≤ k) :
    Function.Injective (carryPartition ell q k m hq hk) := by
  intro u v huv
  have hd : ∀ i, i < m + 1 → carryDigit ell u i = carryDigit ell v i := by
    intro i hi
    have h := congrArg (fun a : Partitions k ell ((q - 1) * repunitSum ell m) => a.val i) huv
    simpa [carryPartition, pack_apply, hi] using h
  have hc : ∀ i, i ≤ m + 1 → carries u i = carries v i := by
    intro i
    induction i with
    | zero => simp [carries_zero]
    | succ i ih =>
      intro hi
      have h0 := ih (by omega)
      have h1 := hd i (by omega)
      have h2 := carry_digit_balance ell hq u i
      have h3 := carry_digit_balance ell hq v i
      have h4 : ell * carries u (i + 1) = ell * carries v (i + 1) := by omega
      exact Nat.eq_of_mul_eq_mul_left (by omega) h4
  funext i
  apply Fin.ext
  have h := hc (i.val + 1) (by omega)
  simpa [carries, show 0 < i.val + 1 ∧ i.val + 1 ≤ m by omega] using h

/-- On the plateau `(q - 1) * (ell + 1) ≤ k ≤ q * ell - 1`, the input
`(q - 1) * (1 + ell + ... + ell ^ m)` has exactly `q ^ m` bounded-digit representations. -/
theorem count_plateau (ell q k m : ℕ) (hell : 2 ≤ ell) (hq : 2 ≤ q) (hqe : q ≤ ell)
    (hk : (q - 1) * (ell + 1) ≤ k) (hk' : k ≤ q * ell - 1) :
    count k ell ((q - 1) * repunitSum ell m) = q ^ m := by
  apply Nat.le_antisymm
  · apply count_le_pow ell q m k _ hell (by omega) hk'
    have h1 := repunit_top ell m (by omega)
    have h2 : (q - 1) * repunitSum ell m ≤ (ell - 1) * repunitSum ell m :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · have := partitions_finite k ell ((q - 1) * repunitSum ell m) hell
    have h := Nat.card_le_card_of_injective (carryPartition ell q k m (by omega) hk)
      (carry_partition_injective ell q k m (by omega) (by omega) hk)
    simpa [Nat.card_fun, count] using h

private lemma readout_upper (ell q k n : ℕ) (hell : 2 ≤ ell) (hq : 1 ≤ q)
    (hk : ell - 1 ≤ k) (hk' : k ≤ q * ell - 1) (hn : 2 ≤ n) :
    readout k ell n ≤ Real.log q / Real.log ell := by
  set m := Nat.log ell n
  have hlt : n < ell ^ (m + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hge : ell ^ m ≤ n := Nat.pow_log_le_self ell (by omega)
  have hcount : count k ell n ≤ q ^ m := count_le_pow ell q m k n hell hq hk' hlt
  have hc : (0 : ℝ) < (count k ell n : ℝ) := by
    exact_mod_cast count_positive k ell n hell hk
  have hlogell : 0 < Real.log (ell : ℝ) := Real.log_pos (by exact_mod_cast hell)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hq1 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have h1 : Real.log (count k ell n : ℝ) ≤ m * Real.log (q : ℝ) := by
    rw [← Real.log_pow]
    apply Real.log_le_log hc
    exact_mod_cast hcount
  have h2 : (m : ℝ) * Real.log (ell : ℝ) ≤ Real.log (n : ℝ) := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast hge
  unfold readout
  rw [div_le_div_iff₀ hlogn hlogell]
  calc Real.log (count k ell n : ℝ) * Real.log (ell : ℝ)
      ≤ (m * Real.log (q : ℝ)) * Real.log (ell : ℝ) :=
        mul_le_mul_of_nonneg_right h1 hlogell.le
    _ = ((m : ℝ) * Real.log (ell : ℝ)) * Real.log (q : ℝ) := by ring
    _ ≤ Real.log (n : ℝ) * Real.log (q : ℝ) := mul_le_mul_of_nonneg_right h2 hq1
    _ = Real.log (q : ℝ) * Real.log (n : ℝ) := by ring

private lemma readout_plateau_lower (ell q k m : ℕ) (hell : 2 ≤ ell) (hq : 2 ≤ q)
    (hqe : q ≤ ell) (hk : (q - 1) * (ell + 1) ≤ k) (hk' : k ≤ q * ell - 1) (hm : 1 ≤ m) :
    (m : ℝ) * (Real.log q / Real.log ell) / (m + 1) ≤
      readout k ell ((q - 1) * repunitSum ell m) := by
  set n := (q - 1) * repunitSum ell m
  have hpow : ell ≤ ell ^ m := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ ell) hm
  have hn : 2 ≤ n := by
    have h1 := pow_le_repunit ell m
    have h2 : repunitSum ell m ≤ n := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hnlt : n < ell ^ (m + 1) := by
    have h1 := repunit_top ell m (by omega)
    have h2 : n ≤ (ell - 1) * repunitSum ell m := Nat.mul_le_mul_right _ (by omega)
    omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hlogell : 0 < Real.log (ell : ℝ) := Real.log_pos (by exact_mod_cast hell)
  have hq1 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hlog : Real.log (n : ℝ) ≤ (m + 1) * Real.log (ell : ℝ) := by
    rw [← Nat.cast_one, ← Nat.cast_add, ← Real.log_pow]
    apply Real.log_le_log hnpos
    exact_mod_cast hnlt.le
  unfold readout
  rw [count_plateau ell q k m hell hq hqe hk hk', Nat.cast_pow, Real.log_pow]
  rw [div_le_div_iff₀ (by positivity) hlogn]
  rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ hlogell]
  have hmq : 0 ≤ (m : ℝ) * Real.log (q : ℝ) := mul_nonneg (by positivity) hq1
  calc (m : ℝ) * Real.log (q : ℝ) * Real.log (n : ℝ)
      ≤ (m : ℝ) * Real.log (q : ℝ) * ((m + 1) * Real.log (ell : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog hmq
    _ = (m : ℝ) * Real.log (q : ℝ) * ((m : ℝ) + 1) * Real.log (ell : ℝ) := by ring

/-- On the plateau `(q - 1) * (ell + 1) ≤ k ≤ q * ell - 1`, the upper logarithmic growth
exponent equals `log q / log ell`. -/
theorem exponent_plateau (ell q k : ℕ) (hell : 2 ≤ ell) (hq : 2 ≤ q) (hqe : q ≤ ell)
    (hk : (q - 1) * (ell + 1) ≤ k) (hk' : k ≤ q * ell - 1) :
    exponent k ell = ((Real.log q / Real.log ell : ℝ) : EReal) := by
  set c : ℝ := Real.log q / Real.log ell
  have hk0 : ell - 1 ≤ k := by
    have : ell + 1 ≤ (q - 1) * (ell + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have htail : ∀ N : ℕ, 2 ≤ N →
      (⨆ (n : ℕ) (_ : N ≤ n), (readout k ell n : EReal)) = (c : EReal) := by
    intro N hN
    apply le_antisymm
    · exact iSup₂_le fun n hn =>
        EReal.coe_le_coe (readout_upper ell q k n hell (by omega) hk0 hk' (by omega))
    · apply le_of_not_gt
      intro hlt
      obtain ⟨r, hsr, hrc⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
      have hr : r < c := EReal.coe_lt_coe_iff.mp hrc
      have hd : 0 < c - r := by linarith
      obtain ⟨m, hm⟩ := exists_nat_gt (max (N : ℝ) (r / (c - r)))
      have hmN : N < m := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hm)
      have hmr : r / (c - r) < (m : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
      have hfrac : r < (m : ℝ) * c / (m + 1) := by
        have hmul := (div_lt_iff₀ hd).mp hmr
        apply (lt_div_iff₀ (by positivity : (0 : ℝ) < m + 1)).mpr
        nlinarith
      have hm1 : 1 ≤ m := by omega
      have hmn : m < ell ^ m := Nat.lt_pow_self (by omega)
      have htailN : N ≤ (q - 1) * repunitSum ell m := by
        have h1 := pow_le_repunit ell m
        have h2 : repunitSum ell m ≤ (q - 1) * repunitSum ell m :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      have hlow := readout_plateau_lower ell q k m hell hq hqe hk hk' hm1
      have hval : (r : EReal) < (readout k ell ((q - 1) * repunitSum ell m) : EReal) :=
        EReal.coe_lt_coe (hfrac.trans_le hlow)
      have hsup : (readout k ell ((q - 1) * repunitSum ell m) : EReal) ≤
          ⨆ (n : ℕ) (_ : N ≤ n), (readout k ell n : EReal) :=
        le_iSup₂_of_le ((q - 1) * repunitSum ell m) htailN le_rfl
      exact (not_lt_of_ge hsup) (hsr.trans hval)
  unfold exponent
  apply le_antisymm
  · exact iInf₂_le_of_le 2 le_rfl (le_of_eq (htail 2 le_rfl))
  · exact le_iInf₂ fun N hN => le_of_eq (htail N hN).symm

end

end D5.S1.Digit.DigitCapPlateau
