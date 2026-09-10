/- GID: D5/S3/Arith/OmegaGreedyPermutation
   generality: G
   mirror-B: D5/B/S3/Arith/OmegaGreedyPermutation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The omega-indexed greedy multiple sequence permutes the positive integers. -/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

open scoped ArithmeticFunction.omega
namespace D5.S3.Arith.OmegaGreedyPermutation

/-- Zero-based enumeration: `prime r` is the (r+1)-st prime. -/
noncomputable def prime (r : ℕ) : ℕ := Nat.nth Nat.Prime r

private theorem prime_prime (r : ℕ) : (prime r).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime r

/-- Minimum of the positive multiples of q outside the finite used set. -/
noncomputable def next (q : ℕ) (used : Finset ℕ) : ℕ :=
  sInf {y | 0 < y ∧ y ∉ used ∧ q ∣ y}

private theorem next_spec (q : ℕ) (used : Finset ℕ) (hq : 0 < q) :
    0 < next q used ∧ next q used ∉ used ∧ q ∣ next q used := by
  apply Nat.sInf_mem (s := {y | 0 < y ∧ y ∉ used ∧ q ∣ y})
  refine ⟨q * (used.sup id + 1), Nat.mul_pos hq (by omega), ?_, dvd_mul_right _ _⟩
  intro hm
  have hb := Finset.le_sup (f := id) hm
  dsimp only [id] at hb
  have := Nat.le_mul_of_pos_left (used.sup id + 1) hq
  omega

/-- Tail state after the seeds 1 and 2, retaining exactly the finite used history. -/
noncomputable def state : ℕ → ℕ × Finset ℕ
  | 0 => (2, {1, 2})
  | k + 1 =>
      let y := next (prime (ω (state k).1 - 1)) (state k).2
      (y, insert y (state k).2)

/-- Tail terms, starting with b(0)=2. -/
noncomputable def b (n : ℕ) : ℕ := (state n).1
/-- Queue selected by the distinct-prime-factor count of the current tail term. -/
noncomputable def q (n : ℕ) : ℕ := prime (ω (b n) - 1)
/-- OEIS indices start at 1; the auxiliary index 0 is assigned 1. -/
noncomputable def seq (n : ℕ) : ℕ := if n ≤ 1 then 1 else b (n - 2)

private theorem step_spec (n : ℕ) :
    0 < b (n + 1) ∧ b (n + 1) ∉ (state n).2 ∧ q n ∣ b (n + 1) :=
  next_spec _ _ (prime_prime _).pos

private theorem b_ge_two (n : ℕ) : 2 ≤ b n := by
  cases n with
  | zero => decide
  | succ n =>
    exact (prime_prime _).two_le.trans
      (Nat.le_of_dvd (step_spec n).1 (step_spec n).2.2)

private theorem used_eq (n : ℕ) :
    (state n).2 = insert 1 ((Finset.range (n + 1)).image b) := by
  induction n with
  | zero => simp [state, b]
  | succ n ih =>
    change insert (b (n + 1)) (state n).2 = _
    rw [ih, Finset.range_add_one (n := n + 1), Finset.image_insert, Finset.insert_comm]

private theorem b_mem_used {i n : ℕ} (hi : i ≤ n) : b i ∈ (state n).2 := by
  rw [used_eq]
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, by simp; omega, rfl⟩)

private theorem b_injective : Function.Injective b := by
  suffices h : ∀ i j, i < j → b i ≠ b j by
    intro i j he
    rcases lt_trichotomy i j with hi | hi | hi
    · exact (h i j hi he).elim
    · exact hi
    · exact (h j i hi he.symm).elim
  intro i j hij he
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact (step_spec k).2.1 (he ▸ b_mem_used (by omega))

private theorem step_le {n m : ℕ} (hm : 0 < m) (hu : m ∉ (state n).2)
    (hd : q n ∣ m) : b (n + 1) ≤ m :=
  Nat.sInf_le ⟨hm, hu, hd⟩

private theorem queue_exhausts (p : ℕ) (hp : p.Prime)
    (hi : {n | q n = p}.Infinite) {m : ℕ} (hm : 0 < m) (hd : p ∣ m) :
    ∃ i, b i = m := by
  by_contra hn
  push Not at hn
  apply hi
  apply Set.Finite.of_injOn (f := fun n => b (n + 1)) (t := Set.Iic m)
  · intro n hq
    apply step_le hm
    · rw [used_eq]
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range, not_or, not_exists]
      refine ⟨?_, fun i he => ?_⟩
      · intro he
        subst m
        exact hp.not_dvd_one hd
      · exact hn i he.2
    · simpa only [Set.mem_ofPred_eq] using hq ▸ hd
  · intro i _ j _ he
    have := b_injective he
    omega
  · exact Set.finite_Iic m



private theorem prime_injective : Function.Injective prime :=
  Nat.nth_injective Nat.infinite_setOfPred_prime

private theorem omega_card (n : ℕ) : ω n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors]

private theorem q_two_of_prime {n : ℕ} (hp : (b n).Prime) : q n = 2 := by
  simp [q, ArithmeticFunction.cardDistinctFactors_apply_prime hp, prime]

private theorem q_appears (n : ℕ) : ∃ i, b i = q n := by
  by_cases hu : q n ∈ (state n).2
  · rw [used_eq] at hu
    rcases Finset.mem_insert.mp hu with h | h
    · exact ((prime_prime _).ne_one h).elim
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact ⟨i, hi⟩
  · refine ⟨n + 1, Nat.le_antisymm ?_ ?_⟩
    · exact step_le (prime_prime _).pos hu (dvd_refl _)
    · exact Nat.le_of_dvd (step_spec n).1 (step_spec n).2.2

private theorem finite_queues_of_finite_two (h : {n | q n = 2}.Finite) :
    (Set.range q).Finite := by
  apply (h.image b).subset
  rintro p ⟨n, rfl⟩
  obtain ⟨i, hi⟩ := q_appears n
  refine ⟨i, q_two_of_prime ?_, hi⟩
  rw [hi]
  exact prime_prime _

private theorem finite_counts_of_finite_queues (h : (Set.range q).Finite) :
    (Set.range (fun n => ω (b n))).Finite := by
  apply Set.Finite.of_injOn (f := fun r => prime (r - 1)) (t := Set.range q)
  · rintro r ⟨n, rfl⟩
    exact ⟨n, rfl⟩
  · rintro r ⟨n, rfl⟩ s ⟨k, rfl⟩ he
    change ω (b n) = ω (b k)
    have he' := prime_injective he
    change ω (b n) - 1 = ω (b k) - 1 at he'
    have hn := ArithmeticFunction.cardDistinctFactors_pos.mpr (b_ge_two n)
    have hk := ArithmeticFunction.cardDistinctFactors_pos.mpr (b_ge_two k)
    omega
  · exact h

private theorem infinite_queue_of_finite_range (h : (Set.range q).Finite) :
    ∃ p, p.Prime ∧ {n | q n = p}.Infinite := by
  by_contra hn
  push Not at hn
  apply Set.infinite_univ (α := ℕ)
  apply Set.Finite.of_finite_fibers q (by simpa using h)
  rintro p ⟨n, _, rfl⟩
  rw [Set.univ_inter]
  change Set.Finite {k | q k = q n}
  exact hn (q n) (prime_prime _)

private theorem large_count_multiple (p K : ℕ) (hp : p.Prime) :
    ∃ m, 0 < m ∧ p ∣ m ∧ K ≤ ω m := by
  let S := (Finset.range K).image prime
  have hS : ∀ x ∈ S, x.Prime := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact prime_prime _
  have hprod : 0 < ∏ x ∈ S, x := Finset.prod_pos (fun x hx => (hS x hx).pos)
  refine ⟨p * ∏ x ∈ S, x, Nat.mul_pos hp.pos hprod, dvd_mul_right _ _, ?_⟩
  have hsub : S ⊆ (p * ∏ x ∈ S, x).primeFactors := by
    nth_rw 1 [← Nat.primeFactors_prod hS]
    exact Nat.primeFactors_mono (dvd_mul_left _ _) (Nat.mul_pos hp.pos hprod).ne'
  have hcard : S.card = K := by
    rw [Finset.card_image_of_injective _ prime_injective, Finset.card_range]
  rw [omega_card, ← hcard]
  exact Finset.card_le_card hsub

private theorem two_queue_infinite : {n | q n = 2}.Infinite := by
  intro hfinite
  have hq := finite_queues_of_finite_two hfinite
  obtain ⟨K, hK⟩ := (finite_counts_of_finite_queues hq).bddAbove
  obtain ⟨p, hp, hi⟩ := infinite_queue_of_finite_range hq
  obtain ⟨m, hm, hd, hw⟩ := large_count_multiple p (K + 1) hp
  obtain ⟨n, hn⟩ := queue_exhausts p hp hi hm hd
  have hle := hK (Set.mem_range_self n)
  rw [hn] at hle
  omega



private theorem even_count_infinite (r : ℕ) :
    {m | 0 < m ∧ 2 ∣ m ∧ ω m = r + 1}.Infinite := by
  let S := (Finset.range (r + 1)).image prime
  let P := ∏ p ∈ S, p
  have hS : ∀ p ∈ S, p.Prime := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact prime_prime _
  have hP : 0 < P := Finset.prod_pos (fun p hp => (hS p hp).pos)
  have htwo : 2 ∈ S := by
    apply Finset.mem_image.mpr
    exact ⟨0, by simp, Nat.nth_prime_zero_eq_two⟩
  have hcard : S.card = r + 1 := by
    rw [Finset.card_image_of_injective _ prime_injective, Finset.card_range]
  let f := fun t : ℕ => 2 ^ (t + 1) * P
  have hfi : Function.Injective f := by
    intro i j he
    have hpow : 2 ^ (i + 1) = 2 ^ (j + 1) := Nat.eq_of_mul_eq_mul_right hP he
    have := Nat.pow_right_injective (by decide : 2 ≤ 2) hpow
    omega
  apply (Set.infinite_range_of_injective hfi).mono
  rintro m ⟨t, rfl⟩
  refine ⟨Nat.mul_pos (pow_pos (by decide) _) hP, ?_, ?_⟩
  · exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega : t + 1 ≠ 0)) P
  · change ω (2 ^ (t + 1) * P) = r + 1
    rw [omega_card, Nat.primeFactors_mul (by positivity) hP.ne',
      Nat.primeFactors_pow_succ, Nat.Prime.primeFactors Nat.prime_two]
    change ({2} ∪ (∏ p ∈ S, p).primeFactors).card = r + 1
    rw [Nat.primeFactors_prod hS, Finset.singleton_union, Finset.insert_eq_of_mem htwo, hcard]

private theorem all_queues_infinite (r : ℕ) : {n | q n = prime r}.Infinite := by
  intro hf
  have hfinite : (b '' {n | q n = prime r}).Finite := hf.image b
  apply even_count_infinite r
  apply hfinite.subset
  intro m hm
  obtain ⟨n, hn⟩ := queue_exhausts 2 Nat.prime_two two_queue_infinite hm.1 hm.2.1
  refine ⟨n, ?_, hn⟩
  change prime (ω (b n) - 1) = prime r
  rw [hn, hm.2.2, Nat.add_sub_cancel]

private theorem tail_surjective {m : ℕ} (hm : 2 ≤ m) : ∃ n, b n = m := by
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hr : prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
  apply queue_exhausts p hp
  · rw [← hr]
    exact all_queues_infinite _
  · omega
  · exact hd

private theorem seq_tail (n : ℕ) : seq (n + 2) = b n := by
  simp [seq, show ¬ n + 2 ≤ 1 by omega]

/-- A363956 starts with the prescribed two seeds. -/
theorem sequence_initial : seq 1 = 1 ∧ seq 2 = 2 := by
  norm_num [seq, b, state]

/-- Every term at a positive index is positive. -/
theorem sequence_positive (n : ℕ) : 0 < seq n := by
  unfold seq
  split
  · omega
  · exact lt_of_lt_of_le (by decide : 0 < 2) (b_ge_two _)

/-- The least-unused recursion never repeats a positive-index term. -/
theorem sequence_injective {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (he : seq i = seq j) : i = j := by
  by_cases hi1 : i ≤ 1 <;> by_cases hj1 : j ≤ 1
  · omega
  · have hb := b_ge_two (j - 2)
    simp only [seq, if_pos hi1, if_neg hj1] at he
    omega
  · have hb := b_ge_two (i - 2)
    simp only [seq, if_pos hj1, if_neg hi1] at he
    omega
  · simp only [seq, if_neg hi1, if_neg hj1] at he
    have := b_injective he
    omega

private theorem used_seq (k : ℕ) :
    (state k).2 = (Finset.range (k + 2)).image (fun i => seq (i + 1)) := by
  induction k with
  | zero =>
    simpa [state, Finset.range_add_one, seq, b] using Finset.pair_comm 1 2
  | succ k ih =>
    change insert (b (k + 1)) (state k).2 = _
    rw [ih, Finset.range_add_one (n := k + 2), Finset.image_insert]
    rw [show k + 2 + 1 = (k + 1) + 2 by omega, seq_tail]

/-- Every later term is exactly the smallest positive unused multiple of the
prime indexed by the previous term's number of distinct prime factors. -/
theorem sequence_greedy (k : ℕ) :
    seq (k + 3) = sInf {y | 0 < y ∧
      (∀ i ∈ Finset.range (k + 2), y ≠ seq (i + 1)) ∧
      prime (ω (seq (k + 2)) - 1) ∣ y} := by
  rw [show k + 3 = (k + 1) + 2 by omega, seq_tail, seq_tail]
  change next (q k) (state k).2 = _
  unfold next
  rw [used_seq]
  congr 1
  ext y
  simp [eq_comm, q]

/-- Every positive integer occurs in OEIS A363956. -/
theorem a363956_surjective (m : ℕ) (hm : 0 < m) : ∃ n, 0 < n ∧ seq n = m := by
  by_cases h : m = 1
  · exact ⟨1, by decide, h ▸ sequence_initial.1⟩
  · obtain ⟨n, hn⟩ := tail_surjective (by omega : 2 ≤ m)
    exact ⟨n + 2, by omega, (seq_tail n).trans hn⟩

#print axioms sequence_initial
#print axioms sequence_positive
#print axioms sequence_injective
#print axioms sequence_greedy
#print axioms a363956_surjective
end D5.S3.Arith.OmegaGreedyPermutation
