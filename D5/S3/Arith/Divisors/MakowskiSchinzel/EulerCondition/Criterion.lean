/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Criterion
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Criterion
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: The odd predecessor abundancy bounds the sigma-totient ratio. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.Fermat
import D5.S3.Arith.Divisors.MakowskiSchinzel.PrimeDeletion

/-! The odd predecessor criterion and its strict non-Fermat improvement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel.EulerCondition

open Finset UniqueFactorizationMonoid

/-- Odd part of the product of the non-Fermat prime predecessors. -/
noncomputable def oddPredecessorPart (n : ℕ) : ℕ :=
  ordCompl[2] (∏ q ∈ nonFermatFactors n, (q - 1))

/-- Abundancy of the odd predecessor part times the non-Fermat Euler factors. -/
noncomputable def psi (n : ℕ) : ℚ :=
  (oddPredecessorPart n).abundancyIndex *
    ∏ q ∈ nonFermatFactors n, (1 - (q : ℚ)⁻¹)

private theorem psi_pos (n : ℕ) : 0 < psi n := by
  classical
  have hq (q : ℕ) (hq : q ∈ nonFermatFactors n) : 1 < q :=
    (Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1).one_lt
  have hP : (∏ q ∈ nonFermatFactors n, (q - 1)) ≠ 0 :=
    (prod_pos fun q h => by have := hq q h; omega).ne'
  have hU : oddPredecessorPart n ≠ 0 := (Nat.ordCompl_pos 2 hP).ne'
  have hA := Nat.abundancyIndex_le_of_dvd hU (one_dvd (oddPredecessorPart n))
  have hA' : 1 ≤ (oddPredecessorPart n).abundancyIndex := by
    simpa [Nat.abundancyIndex] using hA
  apply mul_pos (by linarith : 0 < (oddPredecessorPart n).abundancyIndex)
  apply prod_pos
  intro q h
  apply sub_pos.mpr
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq q h)

private theorem psi_radical (n : ℕ) : psi (radical n) = psi n := by
  classical
  simp [psi, oddPredecessorPart, nonFermatFactors, Nat.primeFactors_radical]

private theorem nonFermatFactors_two_mul (n : ℕ) :
    nonFermatFactors (2 * n) = nonFermatFactors n := by
  classical
  by_cases hn : n = 0
  · simp [hn, nonFermatFactors]
  unfold nonFermatFactors
  rw [Nat.primeFactors_mul (by decide : 2 ≠ 0) hn, Nat.prime_two.primeFactors]
  ext q
  simp only [mem_filter, mem_union, mem_singleton]
  tauto

private theorem psi_two_mul (n : ℕ) : psi (2 * n) = psi n := by
  simp only [psi, oddPredecessorPart, nonFermatFactors_two_mul]

private theorem abundancy_two_pow_lt (A : ℕ) :
    (2 ^ A).abundancyIndex < (2 * 2 ^ A).abundancyIndex := by
  rw [← pow_succ', abundancy_prime_pow Nat.prime_two,
    abundancy_prime_pow Nat.prime_two]
  simp only [geom, sum_range_succ]
  have hh : 0 < ((2 : ℚ)⁻¹) ^ (A + 1) := by positivity
  linarith

private theorem odd_squarefree_psi_le_alpha {m : ℕ} (hm : Odd m)
    (hsq : Squarefree m) :
    psi m ≤ alpha m ∧ ((nonFermatFactors m).Nonempty → psi m < alpha m) := by
  classical
  let Q := nonFermatFactors m
  let F := m.primeFactors \ Q
  let f := ∏ p ∈ F, p
  let P := ∏ q ∈ Q, (q - 1)
  let U := oddPredecessorPart m
  let W := ∏ q ∈ Q, (1 - (q : ℚ)⁻¹)
  let H := ∏ p ∈ F, (1 - (p : ℚ)⁻¹)
  have hsub : Q ⊆ m.primeFactors := filter_subset _ _
  have hp (p : ℕ) (h : p ∈ m.primeFactors) : p.Prime :=
    Nat.prime_of_mem_primeFactors h
  have hodd (p : ℕ) (h : p ∈ m.primeFactors) : Odd p :=
    hm.of_dvd_nat (Nat.dvd_of_mem_primeFactors h)
  have hFpow (p : ℕ) (h : p ∈ F) : ∃ k : ℕ, p - 1 = 2 ^ k := by
    by_contra hnot
    apply (mem_sdiff.mp h).2
    exact mem_filter.mpr ⟨(mem_sdiff.mp h).1,
      ⟨fun he => (hodd p (mem_sdiff.mp h).1).not_two_dvd_nat
        (by rw [he]), hnot⟩⟩
  have hf0 : f ≠ 0 := (prod_pos fun p h => (hp p (mem_sdiff.mp h).1).pos).ne'
  have hfmul : f * (∏ q ∈ Q, q) = m :=
    (prod_sdiff hsub).trans (Nat.prod_primeFactors_of_squarefree hsq)
  have hfdvd : f ∣ m := ⟨_, hfmul.symm⟩
  have hfsq : Squarefree f := hsq.squarefree_of_dvd hfdvd
  have hfo : Odd f := hm.of_dvd_nat hfdvd
  have hpf : f.primeFactors = F :=
    Nat.primeFactors_prod fun p h => hp p (mem_sdiff.mp h).1
  have hphif : f.totient = ∏ p ∈ F, (p - 1) := by
    rw [D5.S3.Factorization.LehmerTotientDichotomy.totient_eq_primeFactors_sub_one_prod
      hf0 hfsq, hpf]
  obtain ⟨A, hA⟩ : ∃ A : ℕ, f.totient = 2 ^ A := by
    rw [hphif]
    have : ∀ S : Finset ℕ, (∀ p ∈ S, ∃ k : ℕ, p - 1 = 2 ^ k) →
        ∃ A : ℕ, (∏ p ∈ S, (p - 1)) = 2 ^ A := by
      intro S
      induction S using Finset.induction_on with
      | empty => exact fun _ => ⟨0, by simp⟩
      | @insert p S hpS ih =>
        intro h
        obtain ⟨a, ha⟩ := h p (mem_insert_self p S)
        obtain ⟨b, hb⟩ := ih (fun q hq => h q (mem_insert_of_mem hq))
        exact ⟨a + b, by rw [prod_insert hpS, ha, hb, pow_add]⟩
    exact this F hFpow
  have hphim : m.totient = f.totient * P := by
    rw [D5.S3.Factorization.LehmerTotientDichotomy.totient_eq_primeFactors_sub_one_prod
      hsq.ne_zero hsq, hphif]
    exact (prod_sdiff hsub).symm
  have hP0 : P ≠ 0 := (prod_pos fun q h => by
    have := (hp q (hsub h)).one_lt
    omega).ne'
  have hU0 : U ≠ 0 := (Nat.ordCompl_pos 2 hP0).ne'
  have hUc : Nat.Coprime 2 U := Nat.coprime_ordCompl Nat.prime_two hP0
  have hUd : U ∣ P := Nat.ordCompl_dvd P 2
  have hUpos : 0 < U.abundancyIndex := by
    have hh := Nat.abundancyIndex_le_of_dvd hU0 (one_dvd U)
    have hh' : 1 ≤ U.abundancyIndex := by simpa [Nat.abundancyIndex] using hh
    linarith
  have hHpos : 0 < H := by
    apply prod_pos
    intro p h
    apply sub_pos.mpr
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (hp p (mem_sdiff.mp h).1).one_lt)
  have hWpos : 0 < W := by
    apply prod_pos
    intro q h
    apply sub_pos.mpr
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (hp q (hsub h)).one_lt)
  have hphi0 : m.totient ≠ 0 := (Nat.totient_pos.mpr hsq.ne_zero.bot_lt).ne'
  have halpha : alpha m = m.totient.abundancyIndex * H * W := by
    rw [alpha_factorization, ← prod_sdiff hsub]
    exact (mul_assoc _ _ _).symm
  have haf : alpha f = f.totient.abundancyIndex * H := by
    rw [alpha_factorization, hpf]
  have hfone : 1 ≤ alpha f := by
    have hh := odd_le_sigma_totient_of_two_pow hfo hA
    rw [alpha, le_div_iff₀ (by exact_mod_cast hf0.bot_lt : (0 : ℚ) < f), one_mul]
    exact_mod_cast hh
  have hbase : f.totient.abundancyIndex * U.abundancyIndex ≤
      m.totient.abundancyIndex := by
    rw [← abundancy_mul (hA ▸ hUc.pow_left A)]
    apply Nat.abundancyIndex_le_of_dvd hphi0
    rw [hphim]
    exact mul_dvd_mul_left f.totient hUd
  have hstart : psi m ≤ alpha f * psi m := by
    simpa using mul_le_mul_of_nonneg_right hfone (psi_pos m).le
  have hfinish : alpha f * psi m ≤ alpha m := by
    rw [halpha, haf]
    change f.totient.abundancyIndex * H * (U.abundancyIndex * W) ≤ _
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbase hHpos.le) hWpos.le]
  refine ⟨hstart.trans hfinish, ?_⟩
  intro hQ
  obtain ⟨q, hq⟩ := hQ
  have hP2 : 2 ∣ P := by
    have hpred : 2 ∣ q - 1 := by
      have hh := hodd q (hsub hq)
      obtain ⟨k, hk⟩ := hh
      exact ⟨k, by omega⟩
    exact hpred.trans (dvd_prod_of_mem _ hq)
  have hdiv : 2 * f.totient * U ∣ m.totient := by
    rw [hphim]
    have hh := hUc.mul_dvd_of_dvd_of_dvd hP2 hUd
    convert mul_dvd_mul_left f.totient hh using 1 <;> ring
  have hcop : (2 * f.totient).Coprime U := by
    rw [hA, ← pow_succ']
    exact hUc.pow_left (A + 1)
  have hstrong : (2 * f.totient).abundancyIndex * U.abundancyIndex ≤
      m.totient.abundancyIndex := by
    rw [← abundancy_mul hcop]
    exact Nat.abundancyIndex_le_of_dvd hphi0 hdiv
  have hlt : f.totient.abundancyIndex < (2 * f.totient).abundancyIndex := by
    rw [hA]
    exact abundancy_two_pow_lt A
  have hh := mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hlt hUpos) hHpos) hWpos
  have hfin := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hstrong hHpos.le) hWpos.le
  rw [halpha]
  apply hstart.trans_lt
  rw [haf]
  change f.totient.abundancyIndex * H * (U.abundancyIndex * W) < _
  nlinarith

/-- The odd predecessor factor bounds the sigma-totient sum, strictly off Fermat support. -/
theorem psi_mul_le_sigma_totient (n : ℕ) :
    psi n * n ≤ 2 * (ArithmeticFunction.sigma 1 n.totient : ℚ) ∧
      (Odd n → psi n * n ≤ (ArithmeticFunction.sigma 1 n.totient : ℚ)) ∧
      ((nonFermatFactors n).Nonempty →
        psi n * n < 2 * (ArithmeticFunction.sigma 1 n.totient : ℚ) ∧
          (Odd n → psi n * n < (ArithmeticFunction.sigma 1 n.totient : ℚ))) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [nonFermatFactors]
  have hnq : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let d := radical n
  have hdsq : Squarefree d := squarefree_radical
  have hpsi : psi d = psi n := psi_radical n
  have hQ : nonFermatFactors d = nonFermatFactors n := by
    simp [d, nonFermatFactors, Nat.primeFactors_radical]
  have hrad : alpha d ≤ alpha n := alpha_radical_le hn
  have hhalf : psi n ≤ 2 * alpha d ∧
      ((nonFermatFactors n).Nonempty → psi n < 2 * alpha d) := by
    rcases Nat.even_or_odd d with he | ho
    · obtain ⟨m, hm⟩ := he
      have hdm : d = 2 * m := by omega
      have hmsq : Squarefree m := hdsq.squarefree_of_dvd
        (by rw [hdm]; exact dvd_mul_left m 2)
      have hmo : Odd m := by
        rcases Nat.even_or_odd m with ⟨k, hk⟩ | hmo
        · exfalso
          apply Nat.squarefree_iff_prime_squarefree.mp hdsq 2 Nat.prime_two
          exact ⟨k, by omega⟩
        · exact hmo
      have hpsim : psi m = psi n := by
        rw [← psi_two_mul m, ← hdm, hpsi]
      have hQm : nonFermatFactors m = nonFermatFactors n := by
        rw [← nonFermatFactors_two_mul m, ← hdm, hQ]
      have hc := odd_squarefree_psi_le_alpha hmo hmsq
      rw [hdm, alpha_two_mul hmo]
      constructor
      · linarith [hc.1]
      · intro hne
        have hh := hc.2 (hQm.symm ▸ hne)
        linarith
    · have hc := odd_squarefree_psi_le_alpha ho hdsq
      constructor
      · have hh := (psi_pos d)
        rw [hpsi] at hh hc
        linarith [hc.1]
      · intro hne
        have hh := hc.2 (hQ.symm ▸ hne)
        have hhpos := psi_pos d
        rw [hpsi] at hh hhpos
        linarith
  have hodd (ho : Odd n) : psi n ≤ alpha n ∧
      ((nonFermatFactors n).Nonempty → psi n < alpha n) := by
    have hdo : Odd d := ho.of_dvd_nat radical_dvd_self
    have hc := odd_squarefree_psi_le_alpha hdo hdsq
    constructor
    · rw [hpsi] at hc
      exact hc.1.trans hrad
    · intro hne
      have hh := (hc.2 (hQ.symm ▸ hne)).trans_le hrad
      rwa [hpsi] at hh
  have hmul : alpha n * n = (ArithmeticFunction.sigma 1 n.totient : ℚ) := by
    rw [alpha, div_mul_cancel₀ _ hnq.ne']
  refine ⟨?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_right (hhalf.1.trans
      (mul_le_mul_of_nonneg_left hrad (by norm_num : (0 : ℚ) ≤ 2))) hnq.le
    simpa only [mul_assoc, hmul] using hh
  · intro ho
    have hh := mul_le_mul_of_nonneg_right (hodd ho).1 hnq.le
    rwa [hmul] at hh
  · intro hne
    constructor
    · have hh := mul_lt_mul_of_pos_right ((hhalf.2 hne).trans_le
        (mul_le_mul_of_nonneg_left hrad (by norm_num : (0 : ℚ) ≤ 2))) hnq
      simpa only [mul_assoc, hmul] using hh
    · intro ho
      have hh := mul_lt_mul_of_pos_right ((hodd ho).2 hne) hnq
      rwa [hmul] at hh


end D5.S3.Arith.MakowskiSchinzel.EulerCondition
