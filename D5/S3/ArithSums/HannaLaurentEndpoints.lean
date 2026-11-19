/- GID: D5/S3/ArithSums/HannaLaurentEndpoints
   generality: I
   mirror-B: D5/B/S3/ArithSums/HannaLaurentEndpoints
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The A391810 coefficients at x^(-m^2) and x^(-(m^2-1)) in rows 2m-1 and 2m. -/

import D5.S3.ArithSums.HannaLaurentDivisorFormula

/-! # Endpoint and penultimate coefficients of the A391810 Laurent rows

For `m ≥ 1`, the coefficient of `x^(-m^2)` is `(-1)^(m-1)` in row `2m-1` and `(-1)^(m-1) m`
in row `2m`; for `m ≥ 2`, the coefficient of `x^(-(m^2-1))` is `2(-1)^m` in row `2m-1` and
`2m(-1)^m` in row `2m`.
-/

namespace D5.S3.ArithSums.HannaLaurentEndpoints

open D5.S3.ArithSums.HannaLaurentRowSums
open D5.S3.ArithSums.HannaLaurentDivisorFormula

/-- The summand of the divisor formula. -/
private def term (n k h : ℕ) : ℚ := (-1 : ℚ) ^ (k / h - 1) * ((n - h).choose (k / h - 1) : ℚ)

private lemma term_zero {n k h : ℕ} (hn : h ≤ n)
    (hlt : n + 1 < h + k / h) : term n k h = 0 := by
  unfold term
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

private lemma coeff_eq (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k) :
    (series n hn).coeff (-(k : ℤ)) = ∑ h ∈ (Nat.divisors k).filter (· ≤ n), term n k h :=
  (divisor_formula n hn).2.1 k hk

private lemma mem_S {n k h : ℕ} :
    h ∈ (Nat.divisors k).filter (· ≤ n) ↔ (h ∣ k ∧ k ≠ 0) ∧ h ≤ n := by
  simp [Nat.mem_divisors]

/-- Complementary divisor arithmetic: if `h * q = k` then `k / h = q`. -/
private lemma div_of_mul {h q k : ℕ} (hh : 0 < h) (e : h * q = k) : k / h = q := by
  rw [← e, Nat.mul_div_cancel_left _ hh]

private lemma sq_case {h q m : ℕ} (e : h * q = m ^ 2) (hs : h + q ≤ 2 * m) : h = m := by
  have hz : ((h : ℤ) - q) ^ 2 ≤ 0 := by
    have e' : (h : ℤ) * q = (m : ℤ) ^ 2 := by exact_mod_cast e
    have hs' : (h : ℤ) + q ≤ 2 * m := by exact_mod_cast hs
    nlinarith [sq_nonneg ((h : ℤ) + q), sq_nonneg ((h : ℤ) - q)]
  have hq : (h : ℤ) = q := by nlinarith [sq_nonneg ((h : ℤ) - q)]
  have hq' : h = q := by exact_mod_cast hq
  subst hq'
  have : h * h = m * m := by rw [e]; ring
  exact Nat.mul_self_inj.mp this

private lemma sq_sum_ge {h q m : ℕ} (e : h * q = m ^ 2) : 2 * m ≤ h + q := by
  by_contra hlt
  have := sq_case e (by omega)
  subst this
  have : q = h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · subst h0; simp at e; omega
    · have : h * q = h * h := by rw [e]; ring
      exact Nat.eq_of_mul_eq_mul_left h0 this
  omega

private lemma pred_case {h q m : ℕ} (hm : 2 ≤ m) (e : h * q = m ^ 2 - 1)
    (hs : h + q ≤ 2 * m) : (h = m - 1 ∧ q = m + 1) ∨ (h = m + 1 ∧ q = m - 1) := by
  have e' : (h : ℤ) * q = (m : ℤ) ^ 2 - 1 := by
    have : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
    have := congrArg (fun x : ℕ => (x : ℤ)) e
    push_cast [Nat.cast_sub ‹1 ≤ m ^ 2›] at this
    exact this
  have hs' : (h : ℤ) + q ≤ 2 * m := by exact_mod_cast hs
  have hsum : (h : ℤ) + q = 2 * m := by
    by_contra hne
    have hlt : (h : ℤ) + q ≤ 2 * m - 1 := by omega
    have h0 : (0 : ℤ) ≤ h + q := by positivity
    nlinarith [sq_nonneg ((h : ℤ) - q)]
  have hdiff : ((h : ℤ) - q) ^ 2 = 4 := by nlinarith
  have : (h : ℤ) - q = 2 ∨ (h : ℤ) - q = -2 := by
    have hp : ((h : ℤ) - q - 2) * ((h : ℤ) - q + 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases this with h1 | h1
  · right; constructor <;> omega
  · left; constructor <;> omega

private lemma pair_cancel (n k : ℕ) (T : Finset ℕ) (hk : 0 < k) (hodd : Odd (n + 1))
    (hT : ∀ h ∈ T, h ∣ k ∧ h + k / h = n + 1 ∧ k / h ≠ h ∧ k / h ∈ T) :
    ∑ h ∈ T, term n k h = 0 := by
  have hval : ∀ h ∈ T, term n k h = (-1 : ℚ) ^ (k / h - 1) := by
    intro h hh
    obtain ⟨_, hs, _, _⟩ := hT h hh
    unfold term
    rw [show n - h = k / h - 1 by omega, Nat.choose_self]
    simp
  refine Finset.sum_involution (fun h _ => k / h) (fun h hh => ?_) (fun h hh _ => (hT h hh).2.2.1)
    (fun h hh => (hT h hh).2.2.2) (fun h hh => Nat.div_div_self (hT h hh).1 hk.ne')
  obtain ⟨hd, hs, _, hmem⟩ := hT h hh
  rw [hval h hh, hval _ hmem, Nat.div_div_self hd hk.ne']
  have h0 : 0 < h := Nat.pos_of_dvd_of_pos hd hk
  have hq1 : 0 < k / h := Nat.div_pos (Nat.le_of_dvd hk hd) h0
  obtain ⟨q, hqdef⟩ : ∃ q, k / h = q := ⟨_, rfl⟩
  rw [hqdef] at hs hq1 ⊢
  clear hqdef hmem hval hT hd
  obtain ⟨t, ht⟩ := hodd
  rcases Nat.even_or_odd (h - 1) with ⟨r, hr⟩ | ⟨r, hr⟩
  · have ho' : Odd (q - 1) := ⟨t - r - 1, by omega⟩
    rw [Even.neg_one_pow ⟨r, hr⟩, ho'.neg_one_pow]
    ring
  · have he' : Even (q - 1) := ⟨t - r - 1, by omega⟩
    rw [Odd.neg_one_pow ⟨r, hr⟩, he'.neg_one_pow]
    ring

private lemma restrict (n k : ℕ) :
    ∑ h ∈ (Nat.divisors k).filter (· ≤ n), term n k h =
      ∑ h ∈ ((Nat.divisors k).filter (· ≤ n)).filter (fun h => h + k / h ≤ n + 1),
        term n k h := by
  refine (Finset.sum_filter_of_ne fun h hh hne => ?_).symm
  by_contra hc
  exact hne (term_zero (mem_S.mp hh).2 (by omega))

private lemma sq_div (m : ℕ) (hm : 1 ≤ m) : m ^ 2 / m = m := by
  rw [pow_two, Nat.mul_div_cancel _ (by omega)]

private lemma pred_mul (m : ℕ) (hm : 1 ≤ m) : (m - 1) * (m + 1) = m ^ 2 - 1 := by
  apply Nat.eq_sub_of_add_eq
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

/-- Endpoint and penultimate coefficients: for `m ≥ 1`, `T(2m-1, m^2) = (-1)^(m-1)` and
`T(2m, m^2) = (-1)^(m-1) m`; for `m ≥ 2`, `T(2m-1, m^2-1) = 2(-1)^m` and
`T(2m, m^2-1) = 2m(-1)^m`. -/
theorem endpoints (m : ℕ) (hm : 1 ≤ m) :
    (series (2 * m - 1) (by omega)).coeff (-((m ^ 2 : ℕ) : ℤ)) = (-1 : ℚ) ^ (m - 1) ∧
    (series (2 * m) (by omega)).coeff (-((m ^ 2 : ℕ) : ℤ)) = (-1 : ℚ) ^ (m - 1) * m ∧
    (2 ≤ m → (series (2 * m - 1) (by omega)).coeff (-((m ^ 2 - 1 : ℕ) : ℤ)) =
      2 * (-1 : ℚ) ^ m) ∧
    (2 ≤ m → (series (2 * m) (by omega)).coeff (-((m ^ 2 - 1 : ℕ) : ℤ)) =
      2 * m * (-1 : ℚ) ^ m) := by
  have hk : 0 < m ^ 2 := by positivity
  have hmem : ∀ n, m ≤ n → m ∈ (Nat.divisors (m ^ 2)).filter (· ≤ n) := fun n hn =>
    mem_S.mpr ⟨⟨dvd_pow_self m two_ne_zero, hk.ne'⟩, hn⟩
  refine ⟨?_, ?_, fun h2 => ?_, fun h2 => ?_⟩
  · -- row 2m-1, column m^2: only h = m survives
    rw [coeff_eq _ _ _ hk, Finset.sum_eq_single m]
    · unfold term
      rw [sq_div m hm, show 2 * m - 1 - m = m - 1 by omega, Nat.choose_self]
      simp
    · intro b hb hbm
      obtain ⟨⟨hd, _⟩, hbn⟩ := mem_S.mp hb
      have hb0 : 0 < b := Nat.pos_of_dvd_of_pos hd hk
      have e : b * (m ^ 2 / b) = m ^ 2 := Nat.mul_div_cancel' hd
      apply term_zero hbn
      by_contra hc
      exact hbm (sq_case e (by omega))
    · intro hnot
      exact absurd (hmem _ (by omega)) hnot
  · -- row 2m, column m^2: h = m plus cancelling pairs
    rw [coeff_eq _ _ _ hk, restrict _ _]
    set S0 := ((Nat.divisors (m ^ 2)).filter (· ≤ 2 * m)).filter
      (fun h => h + m ^ 2 / h ≤ 2 * m + 1) with hS0
    have hmS0 : m ∈ S0 := by
      rw [hS0, Finset.mem_filter]
      exact ⟨hmem _ (by omega), by rw [sq_div m hm]; omega⟩
    rw [← Finset.add_sum_erase _ _ hmS0]
    have hzero : ∑ h ∈ S0.erase m, term (2 * m) (m ^ 2) h = 0 := by
      apply pair_cancel _ _ _ hk ⟨m, by ring⟩
      intro h hh
      rw [Finset.mem_erase, hS0, Finset.mem_filter, mem_S] at hh
      obtain ⟨hne, ⟨⟨hd, _⟩, hhn⟩, hsum⟩ := hh
      have h0 : 0 < h := Nat.pos_of_dvd_of_pos hd hk
      have e : h * (m ^ 2 / h) = m ^ 2 := Nat.mul_div_cancel' hd
      have hdq : m ^ 2 / (m ^ 2 / h) = h := Nat.div_div_self hd hk.ne'
      have hdvq : m ^ 2 / h ∣ m ^ 2 := Nat.div_dvd_of_dvd hd
      have hge := sq_sum_ge e
      have hne2 : h + m ^ 2 / h ≠ 2 * m := fun heq => hne (sq_case e heq.le)
      have hqne : m ^ 2 / h ≠ h := by
        intro hqh
        have : h * h = m * m := by rw [hqh] at e; rw [e]; ring
        exact hne (Nat.mul_self_inj.mp this)
      have hqm : m ^ 2 / h ≠ m := by
        intro hqm
        rw [hqm] at e
        have : h * m = m * m := by rw [e]; ring
        exact hne (Nat.eq_of_mul_eq_mul_right (by omega) this)
      set q := m ^ 2 / h with hqdef
      refine ⟨hd, by omega, hqne, ?_⟩
      rw [Finset.mem_erase, hS0, Finset.mem_filter, mem_S, hdq]
      exact ⟨hqm, ⟨⟨hdvq, hk.ne'⟩, by omega⟩, by omega⟩
    rw [hzero, add_zero]
    unfold term
    rw [sq_div m hm, show 2 * m - m = m by omega,
      show m.choose (m - 1) = m.choose 1 from (Nat.choose_symm (by omega)).symm.trans
        (by rw [Nat.sub_sub_self hm]), Nat.choose_one_right]
  · -- row 2m-1, column m^2-1: h = m-1 and h = m+1 survive
    have hk1 : 0 < m ^ 2 - 1 := by
      have : 4 ≤ m ^ 2 := by nlinarith
      omega
    have e1 := pred_mul m hm
    rw [coeff_eq _ _ _ hk1, Finset.sum_eq_add (m - 1) (m + 1) (by omega)]
    · unfold term
      rw [show (m ^ 2 - 1) / (m - 1) = m + 1 from div_of_mul (by omega) e1,
        show (m ^ 2 - 1) / (m + 1) = m - 1 from div_of_mul (by omega)
          (by rw [Nat.mul_comm]; exact e1),
        show 2 * m - 1 - (m - 1) = m by omega, show m + 1 - 1 = m by omega,
        show 2 * m - 1 - (m + 1) = m - 2 by omega, show m - 1 - 1 = m - 2 by omega,
        Nat.choose_self, Nat.choose_self]
      have : (-1 : ℚ) ^ (m - 2) = (-1) ^ m := by
        rw [show m = m - 2 + 2 by omega, pow_add]
        simp
      push_cast
      rw [this]
      ring
    · intro c hc hcne
      obtain ⟨⟨hd, _⟩, hcn⟩ := mem_S.mp hc
      have e : c * ((m ^ 2 - 1) / c) = m ^ 2 - 1 := Nat.mul_div_cancel' hd
      apply term_zero hcn
      by_contra hlt
      rcases pred_case h2 e (by omega) with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hcne.1 h1
      · exact hcne.2 h1
    · intro hnot
      exact absurd (mem_S.mpr ⟨⟨Dvd.intro _ e1, hk1.ne'⟩, by omega⟩) hnot
    · intro hnot
      exact absurd (mem_S.mpr ⟨⟨Dvd.intro_left _ e1, hk1.ne'⟩, by omega⟩) hnot
  · -- row 2m, column m^2-1: h = m-1, h = m+1 and cancelling pairs
    have hk1 : 0 < m ^ 2 - 1 := by
      have : 4 ≤ m ^ 2 := by nlinarith
      omega
    have e1 := pred_mul m hm
    have hq1 : (m ^ 2 - 1) / (m - 1) = m + 1 := div_of_mul (by omega) e1
    have hq2 : (m ^ 2 - 1) / (m + 1) = m - 1 :=
      div_of_mul (by omega) (by rw [Nat.mul_comm]; exact e1)
    rw [coeff_eq _ _ _ hk1, restrict _ _]
    set S0 := ((Nat.divisors (m ^ 2 - 1)).filter (· ≤ 2 * m)).filter
      (fun h => h + (m ^ 2 - 1) / h ≤ 2 * m + 1) with hS0
    have ha : m - 1 ∈ S0 := by
      rw [hS0, Finset.mem_filter, mem_S, hq1]
      exact ⟨⟨⟨Dvd.intro _ e1, hk1.ne'⟩, by omega⟩, by omega⟩
    have hb : m + 1 ∈ S0.erase (m - 1) := by
      rw [Finset.mem_erase, hS0, Finset.mem_filter, mem_S, hq2]
      exact ⟨by omega, ⟨⟨Dvd.intro_left _ e1, hk1.ne'⟩, by omega⟩, by omega⟩
    rw [← Finset.add_sum_erase _ _ ha, ← Finset.add_sum_erase _ _ hb]
    have hzero : ∑ h ∈ (S0.erase (m - 1)).erase (m + 1), term (2 * m) (m ^ 2 - 1) h = 0 := by
      apply pair_cancel _ _ _ hk1 ⟨m, by ring⟩
      intro h hh
      rw [Finset.mem_erase, Finset.mem_erase, hS0, Finset.mem_filter, mem_S] at hh
      obtain ⟨hne1, hne2, ⟨⟨hd, _⟩, hhn⟩, hsum⟩ := hh
      have h0 : 0 < h := Nat.pos_of_dvd_of_pos hd hk1
      have e : h * ((m ^ 2 - 1) / h) = m ^ 2 - 1 := Nat.mul_div_cancel' hd
      have hnot : ¬ h + (m ^ 2 - 1) / h ≤ 2 * m := by
        intro hle
        rcases pred_case h2 e hle with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hne2 h1
        · exact hne1 h1
      have hdq : (m ^ 2 - 1) / ((m ^ 2 - 1) / h) = h := Nat.div_div_self hd hk1.ne'
      have e' : ((m ^ 2 - 1) / h) * h = m ^ 2 - 1 := by rw [Nat.mul_comm]; exact e
      have hqne : (m ^ 2 - 1) / h ≠ h := by
        intro hqh
        have : h * h = m ^ 2 - 1 := by rw [hqh] at e; exact e
        have hlo : (m - 1) * (m - 1) < h * h := by
          rw [this, ← e1]; exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        have hhi : h * h < m * m := by rw [this, ← pow_two]; omega
        have h1 : m - 1 < h := Nat.mul_self_lt_mul_self_iff.mp hlo
        have h2' : h < m := Nat.mul_self_lt_mul_self_iff.mp hhi
        omega
      have hdvq : (m ^ 2 - 1) / h ∣ m ^ 2 - 1 := Nat.div_dvd_of_dvd hd
      set q := (m ^ 2 - 1) / h with hqdef
      refine ⟨hd, by omega, hqne, ?_⟩
      rw [Finset.mem_erase, Finset.mem_erase, hS0, Finset.mem_filter, mem_S, hdq]
      have key : h * q = (m - 1) * (m + 1) := e.trans e1.symm
      refine ⟨fun hq => ?_, fun hq => ?_, ⟨⟨hdvq, hk1.ne'⟩, by omega⟩, by omega⟩
      · rw [hq] at key
        exact hne2 (Nat.eq_of_mul_eq_mul_right (by omega) key)
      · rw [hq, Nat.mul_comm (m - 1)] at key
        exact hne1 (Nat.eq_of_mul_eq_mul_right (by omega) key)
    rw [hzero, add_zero]
    unfold term
    rw [hq1, hq2, show 2 * m - (m - 1) = m + 1 by omega, show m + 1 - 1 = m by omega,
      show 2 * m - (m + 1) = m - 1 by omega, show m - 1 - 1 = m - 2 by omega,
      Nat.choose_succ_self_right]
    have hc : (m - 1).choose (m - 2) = m - 1 := by
      rw [show m - 1 = (m - 2) + 1 by omega, Nat.choose_succ_self_right]
    rw [hc]
    have : (-1 : ℚ) ^ (m - 2) = (-1) ^ m := by
      rw [show m = m - 2 + 2 by omega, pow_add]
      simp
    rw [this]
    push_cast [show 1 ≤ m by omega]
    ring

end D5.S3.ArithSums.HannaLaurentEndpoints
