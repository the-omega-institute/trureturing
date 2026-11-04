/- GID: D5/S3/Factorization/ReciprocalSigmaThreshold
   generality: I
   mirror-B: D5/B/S3/Factorization/ReciprocalSigmaThreshold
   mirror-E: none(waiver:universal-inequality)
   anchors: []
   utility: none
   digest: Reciprocal sigma divisor sums and their positive threshold sets. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic

/-! Exact reciprocal-sigma sums on the positive integers. -/

namespace D5.S3.Factorization.ReciprocalSigmaThreshold

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

/-- The exact rational sum over all positive divisors. -/
def g (k : ℕ) : ℚ := ∑ d ∈ k.divisors, 1 / (sigma 1 d : ℚ)

/-- A common least positive element includes nonemptiness of both sets. -/
def claim : Prop := ∀ r : ℕ, 0 < r → ∃ m : ℕ,
  IsLeast {k : ℕ | 0 < k ∧ ⌊g k⌋ = (r : ℤ)} m ∧
  IsLeast {k : ℕ | 0 < k ∧ (r : ℚ) ≤ g k} m

private def reciprocalSigma : ArithmeticFunction ℚ :=
  (ζ : ArithmeticFunction ℚ).pdiv (sigma 1 : ArithmeticFunction ℚ)

private def gAF : ArithmeticFunction ℚ := reciprocalSigma * ζ

private lemma g_eq_af (k : ℕ) : g k = gAF k := by
  rw [gAF, coe_mul_zeta_apply]
  apply sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  simp [reciprocalSigma, pdiv_apply, natCoe_apply, zeta_apply_ne hd0]

private lemma g_mult : gAF.IsMultiplicative :=
  (isMultiplicative_zeta.natCast.pdiv isMultiplicative_sigma.natCast).mul
    isMultiplicative_zeta.natCast

private lemma g_mul {m n : ℕ} (hc : m.Coprime n) : g (m*n) = g m * g n := by
  simp only [g_eq_af]
  exact g_mult.map_mul_of_coprime hc

private lemma g_one : g 1 = 1 := by simp [g]

private lemma g_nonneg (k : ℕ) : 0 ≤ g k := by
  exact sum_nonneg fun d _ => by positivity

private lemma one_le_g {k : ℕ} (hk : 0 < k) : 1 ≤ g k := by
  have hmem : 1 ∈ k.divisors := Nat.one_mem_divisors.mpr (Nat.ne_of_gt hk)
  have h := Finset.single_le_sum (f := fun d => 1 / (sigma 1 d : ℚ))
    (fun d _ => by positivity) hmem
  simpa [g] using h

private lemma g_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    g (p ^ a) = ∑ i ∈ range (a + 1), 1 / (sigma 1 (p ^ i) : ℚ) := by
  exact Nat.sum_divisors_prime_pow hp

private lemma sigma_prime {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  simpa [Finset.sum_range_succ, add_comm] using
    (sigma_one_apply_prime_pow (i := 1) hp)

private lemma sigma_ge_self (d : ℕ) : d ≤ sigma 1 d := by
  by_cases hd : d = 0
  · simp [hd]
  · rw [sigma_one_apply]
    exact single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self d hd)

private lemma prime_sum_le_g (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s, 1 / ((p : ℚ) + 1)) ≤ g (∏ p ∈ s, p) := by
  have hpos : 0 < ∏ p ∈ s, p := prod_pos fun p hp => (hs p hp).pos
  have hsub : s ⊆ (∏ p ∈ s, p).divisors := by
    intro p hp
    exact Nat.mem_divisors.mpr ⟨dvd_prod_of_mem id hp, Nat.ne_of_gt hpos⟩
  calc
    _ = ∑ p ∈ s, 1 / (sigma 1 p : ℚ) := by
      apply sum_congr rfl
      intro p hp
      rw [sigma_prime (hs p hp), Nat.cast_add, Nat.cast_one]
    _ ≤ g (∏ p ∈ s, p) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

private lemma threshold_exists (r : ℕ) : ∃ k : ℕ, 0 < k ∧ (r : ℚ) ≤ g k := by
  by_contra! h
  apply Nat.Primes.not_summable_one_div
  apply summable_of_sum_le (c := 2 * (r : ℝ)) (fun p => by positivity)
  intro s
  let t : Finset ℕ := s.image (fun p : Nat.Primes => (p : ℕ))
  have ht : ∀ p ∈ t, p.Prime := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact q.property
  have hpos : 0 < ∏ p ∈ t, p := prod_pos fun p hp => (ht p hp).pos
  have hbound : (∑ p ∈ t, 1 / ((p : ℝ) + 1)) ≤ (g (∏ p ∈ t, p) : ℝ) := by
    have hb : ((∑ p ∈ t, 1 / ((p : ℚ) + 1) : ℚ) : ℝ) ≤
        (g (∏ p ∈ t, p) : ℝ) := Rat.cast_le.mpr (prime_sum_le_g t ht)
    push_cast at hb
    exact hb
  have himage : (∑ p ∈ t, 1 / ((p : ℝ) + 1)) =
      ∑ p ∈ s, 1 / ((p : ℝ) + 1) := by
    exact sum_image (fun _ _ _ _ heq => Subtype.ext heq)
  rw [himage] at hbound
  have hlt : (g (∏ p ∈ t, p) : ℝ) < (r : ℝ) := by
    exact_mod_cast h _ hpos
  calc
    (∑ p ∈ s, (1 / p : ℝ)) ≤ ∑ p ∈ s, 2 * (1 / ((p : ℝ) + 1)) := by
      apply sum_le_sum
      intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_lt.le
      rw [mul_one_div]
      exact (div_le_div_iff₀ hp0 (by positivity)).mpr (by linarith)
    _ = 2 * ∑ p ∈ s, 1 / ((p : ℝ) + 1) := by rw [mul_sum]
    _ ≤ 2 * (g (∏ p ∈ t, p) : ℝ) := mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ ≤ 2 * (r : ℝ) := by linarith

private lemma g_prime_pow_le {p : ℕ} (hp : p.Prime) (a : ℕ) :
    g (p ^ a) ≤ (p : ℚ) / (p - 1) := by
  have hpq : 1 < (p : ℚ) := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℚ) < p := by linarith
  have hsum : g (p ^ a) ≤ ∑ i ∈ range (a + 1), ((p : ℚ)⁻¹) ^ i := by
    rw [g_prime_pow hp]
    apply sum_le_sum
    intro i hi
    rw [inv_pow, ← one_div]
    apply one_div_le_one_div_of_le (pow_pos hp0 i)
    exact_mod_cast sigma_ge_self (p ^ i)
  have hgeom := geom_sum_mul_neg (p : ℚ)⁻¹ (a + 1)
  have hden : 0 < (1 : ℚ) - (p : ℚ)⁻¹ := by
    have := (inv_lt_one₀ hp0).mpr hpq
    linarith
  have hpow : 0 ≤ ((p : ℚ)⁻¹) ^ (a + 1) := by positivity
  have hbound : (∑ i ∈ range (a + 1), ((p : ℚ)⁻¹) ^ i) ≤
      1 / (1 - (p : ℚ)⁻¹) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have heq : 1 / ((1 : ℚ) - (p : ℚ)⁻¹) = (p : ℚ) / (p - 1) := by
    field_simp
  exact hsum.trans (heq ▸ hbound)

private lemma initial_ratio_product (N : ℕ) (hN : 1 ≤ N) :
    (∏ p ∈ Icc 2 N, (p : ℚ) / (p - 1)) = N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [prod_Icc_succ_top (by omega), ih]
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    push_cast
    simp only [add_sub_cancel_right]
    field_simp
    <;> ring

private lemma g_le_prime_bound {n P : ℕ} (hn : 0 < n) (hP : 1 ≤ P)
    (hmax : ∀ p ∈ n.primeFactors, p ≤ P) : g n ≤ (P : ℚ) := by
  have hfac : g n = ∏ p ∈ n.primeFactors, g (p ^ n.factorization p) := by
    simp only [g_eq_af]
    rw [g_mult.multiplicative_factorization gAF (Nat.ne_of_gt hn),
      Nat.prod_factorization_eq_prod_primeFactors]
  rw [hfac, ← initial_ratio_product P hP]
  refine (prod_le_prod₀ (fun p hp => g_nonneg _) (fun p hp =>
    g_prime_pow_le (Nat.prime_of_mem_primeFactors hp) _)).trans ?_
  apply prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).two_le, hmax p hp⟩
  · intro p hp
    have hpq : (1 : ℚ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact div_nonneg (by positivity) (by linarith)
  · intro p hp _
    have hp2 : 2 ≤ p := (mem_Icc.mp hp).1
    have hpq : (1 : ℚ) < p := by exact_mod_cast (by omega : 1 < p)
    exact (one_le_div (by linarith : (0 : ℚ) < p - 1)).mpr (by linarith)

private lemma g_prime_step {p : ℕ} (hp : p.Prime) (a : ℕ) :
    g (p ^ (a + 1)) ≤ g (p ^ a) * (1 + 1 / ((p : ℚ) + 1)) := by
  have hdiv : p ∣ p ^ (a + 1) := dvd_pow_self p (by omega)
  have hs : sigma 1 p ≤ sigma 1 (p ^ (a + 1)) := by
    rw [sigma_one_apply, sigma_one_apply]
    exact sum_le_sum_of_subset_of_nonneg
      (Nat.divisors_subset_of_dvd (pow_ne_zero _ hp.ne_zero) hdiv)
      (fun _ _ _ => Nat.zero_le _)
  rw [sigma_prime hp] at hs
  have hsQ : (p : ℚ) + 1 ≤ (sigma 1 (p ^ (a + 1)) : ℚ) := by exact_mod_cast hs
  have hinv : 1 / (sigma 1 (p ^ (a + 1)) : ℚ) ≤ 1 / ((p : ℚ) + 1) :=
    one_div_le_one_div_of_le (by positivity) hsQ
  have hg : 1 ≤ g (p ^ a) := one_le_g (pow_pos hp.pos _)
  have hstep : g (p ^ (a + 1)) = g (p ^ a) + 1 / (sigma 1 (p ^ (a + 1)) : ℚ) := by
    rw [g_prime_pow hp, sum_range_succ, ← g_prime_pow hp]
  rw [hstep]
  have hmul := mul_le_mul_of_nonneg_right hg (by positivity : 0 ≤ 1 / ((p : ℚ) + 1))
  nlinarith

private lemma prime_deletion {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpd : p ∣ m) :
    ∃ q : ℕ, 0 < q ∧ q < m ∧ g m ≤ g q * (1 + 1 / ((p : ℚ) + 1)) := by
  obtain ⟨e, u, hnot, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.ne_of_gt hm) p hp.ne_one
  have he : e ≠ 0 := by
    intro he
    simp [he] at heq
    exact hnot (heq ▸ hpd)
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
  have hu : 0 < u := by
    by_contra! hu
    have : u = 0 := by omega
    simp [this] at heq
    omega
  let q := p ^ a * u
  have hq : 0 < q := Nat.mul_pos (pow_pos hp.pos _) hu
  have hmrep : m = p * q := by
    dsimp [q]
    rw [heq, pow_succ]
    ring
  have hc : p.Coprime u := hp.coprime_iff_not_dvd.mpr hnot
  refine ⟨q, hq, ?_, ?_⟩
  · rw [hmrep]
    have := hp.two_le
    nlinarith
  · calc
      g m = g (p ^ (a + 1)) * g u := by rw [heq, g_mul (hc.pow_left _)]
      _ ≤ (g (p ^ a) * (1 + 1 / ((p : ℚ) + 1))) * g u :=
        mul_le_mul_of_nonneg_right (g_prime_step hp a) (g_nonneg u)
      _ = g q * (1 + 1 / ((p : ℚ) + 1)) := by
        dsimp [q]
        rw [g_mul (hc.pow_left _)]
        ring

/-- Every positive threshold has one positive least argument for both predicates. -/
theorem result : claim := by
  classical
  intro r hr
  let hex := threshold_exists r
  let m := Nat.find hex
  have hm : 0 < m ∧ (r : ℚ) ≤ g m := Nat.find_spec hex
  have hmin : ∀ k : ℕ, 0 < k → (r : ℚ) ≤ g k → m ≤ k := by
    intro k hk hkr
    exact Nat.find_min' hex ⟨hk, hkr⟩
  have hfloor : ⌊g m⌋ = (r : ℤ) := by
    apply Int.floor_eq_iff.mpr
    push_cast
    refine ⟨hm.2, ?_⟩
    by_cases hm1 : m = 1
    · rw [hm1, g_one]
      have hrq : (1 : ℚ) ≤ r := by exact_mod_cast hr
      linarith
    · have hne : m ≠ 1 := hm1
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have hpf : p ∈ m.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hpd, Nat.ne_of_gt hm.1⟩
      have hnonempty : m.primeFactors.Nonempty := ⟨p, hpf⟩
      let P := m.primeFactors.max' hnonempty
      have hPmem : P ∈ m.primeFactors := max'_mem _ hnonempty
      have hPprime : P.Prime := Nat.prime_of_mem_primeFactors hPmem
      have hmax : ∀ p ∈ m.primeFactors, p ≤ P := by
        intro p hp
        exact le_max' _ _ hp
      have hgP : g m ≤ (P : ℚ) := g_le_prime_bound hm.1 hPprime.one_lt.le hmax
      have hrP : (r : ℚ) ≤ P := hm.2.trans hgP
      obtain ⟨q, hq, hqm, hdel⟩ := prime_deletion hm.1 hPprime
        (Nat.dvd_of_mem_primeFactors hPmem)
      have hqr : g q < (r : ℚ) := by
        by_contra! hqr
        exact (Nat.not_le_of_gt hqm) (hmin q hq hqr)
      have hfactor : 0 < (1 : ℚ) + 1 / ((P : ℚ) + 1) := by positivity
      have hden : (0 : ℚ) < (P : ℚ) + 1 := by positivity
      have hb : (r : ℚ) / ((P : ℚ) + 1) ≤ 1 :=
        (div_le_one hden).mpr (by linarith)
      calc
        g m ≤ g q * (1 + 1 / ((P : ℚ) + 1)) := hdel
        _ < (r : ℚ) * (1 + 1 / ((P : ℚ) + 1)) :=
          mul_lt_mul_of_pos_right hqr hfactor
        _ = (r : ℚ) + (r : ℚ) / ((P : ℚ) + 1) := by ring
        _ ≤ (r : ℚ) + 1 := by linarith
  refine ⟨m, ⟨⟨hm.1, hfloor⟩, ?_⟩, ⟨hm, ?_⟩⟩
  · intro k hk
    apply hmin k hk.1
    have hf := Int.floor_le (g k)
    rw [hk.2] at hf
    exact_mod_cast hf
  · intro k hk
    exact hmin k hk.1 hk.2

#print claim
#check result
#print axioms result

end D5.S3.Factorization.ReciprocalSigmaThreshold
