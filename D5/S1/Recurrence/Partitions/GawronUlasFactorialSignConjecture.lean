/- GID: D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture
   generality: I
   mirror-B: D5/B/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.claim; result=D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.result; claim=D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.claim
   digest: Factorial partition signs fail on an unbounded even progression. -/
/- admission_basis: open-problem-resolution (#19687; Refuted)
   escape_witness: none
   Direct frozen dependencies: none (pinned Mathlib only).
   proof_shape: U_three: bind-only; consumer: S_coordinates; escape_witness: none.
   proof_shape: parts_card_le: bind-only; consumer: S_eq_partition_sum; escape_witness: none.
   proof_shape: S_eq_partition_sum: bind-only; consumer: S_coordinates; escape_witness: none.
   proof_shape: multiset_126: bind-only; consumer: partition126_inverse; escape_witness: none.
   proof_shape: partition126_parts: bind-only; consumer: partition126_counts, partition126_inverse, S_coordinates; escape_witness: none.
   proof_shape: partition126_counts: bind-only; consumer: S_coordinates; escape_witness: none.
   proof_shape: partition126_inverse: bind-only; consumer: S_coordinates; escape_witness: none.
   proof_shape: S_coordinates: bind-only; consumer: signed_coordinates; escape_witness: none.
   proof_shape: alternating_quadratic: bind-only; consumer: double_sum; escape_witness: none.
   proof_shape: outer_alternating: bind-only; consumer: cubic; escape_witness: none.
   proof_shape: outer_ordinary: bind-only; consumer: cubic; escape_witness: none.
   proof_shape: signed_coordinates: bind-only; consumer: double_sum; escape_witness: none.
   proof_shape: double_sum: bind-only; consumer: cubic; escape_witness: none.
   proof_shape: cubic: bind-only; consumer: negative_family; escape_witness: none.
   proof_shape: negative_family: bind-only; consumer: result; escape_witness: none.
   proof_shape: result: bind-only; consumer: none; escape_witness: none.
   The source definitions c, S, U and claim retain their source expressions.
   The explicit U 3 factorial instance refutes claim through result.
   The public result is the designated refutation result (`basis=refutes`) and is exempt
   from four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.NumberTheory.Bernoulli

/-! Binding conventions for F. Gawron and M. Ulas, "Signs behaviour of sums of weighted numbers of partitions",
arXiv:2202.05221v1 (Ramanujan J. 60 (2023) 571–584): the number `c_A(i, n)` of `A`-partitions of `n` with exactly `i`
parts, the sums `S_{A,k}(n) = ∑_{i=0}^{n} (−1)^i i^k c_A(i, n)`, the sets `U_m = {i! : i = 1, …, m}`, and Conjecture 4.4:
for `m ≥ 2`, `(−1)^⌊(n+1)/2⌋ S_{U_m,k}(n) ≥ 0` for `n ≫ 0` and each `k ∈ {0, …, m − 2}`; "Moreover, if `k ≥ m − 1` then
`(−1)^n S_{U_m,k}(n) ≥ 0` for `n ≫ 0`". -/

namespace D5.S1.Recurrence.Partitions.GawronUlasFactorialSignConjecture

open Classical in
/-- `c_A(i, n)`: the number of partitions of `n` with every part in `A` and exactly `i` parts. -/
noncomputable def c (A : Set ℕ) (i n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter
    (fun p => (∀ a ∈ p.parts, a ∈ A) ∧ Multiset.card p.parts = i)).card

/-- `S_{A,k}(n) = ∑_{i=0}^{n} (−1)^i i^k c_A(i, n)`. -/
noncomputable def S (A : Set ℕ) (k n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (i : ℤ) ^ k * (c A i n : ℤ)

/-- `U_m = {i! : i = 1, …, m}`. -/
def U (m : ℕ) : Set ℕ :=
  {a | ∃ i, 1 ≤ i ∧ i ≤ m ∧ a = i.factorial}

/-- Conjecture 4.4, both assertions; "for `n ≫ 0`" is "for all sufficiently large `n`". -/
def claim : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    (∀ k : ℕ, k ≤ m - 2 → ∃ N : ℕ, ∀ n ≥ N, 0 ≤ (-1 : ℤ) ^ ((n + 1) / 2) * S (U m) k n) ∧
      (∀ k : ℕ, m - 1 ≤ k → ∃ N : ℕ, ∀ n ≥ N, 0 ≤ (-1 : ℤ) ^ n * S (U m) k n)


open Finset Classical

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

private lemma U_three : U 3 = ({1, 2, 6} : Set ℕ) := by
  ext a
  constructor
  · rintro ⟨i, hi, hi', rfl⟩
    interval_cases i <;> norm_num [Nat.factorial]
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨1, by decide, by decide, by decide⟩
    · exact ⟨2, by decide, by decide, by decide⟩
    · exact ⟨3, by decide, by decide, by decide⟩

private lemma parts_card_le {n : ℕ} (p : Nat.Partition n) : p.parts.card ≤ n := by
  have h := Multiset.card_nsmul_le_sum (s := p.parts) (a := 1) (fun _ h => p.parts_pos h)
  simpa [p.parts_sum] using h


private lemma S_eq_partition_sum (A : Set ℕ) (k n : ℕ) :
    S A k n = ∑ p ∈ (Finset.univ : Finset (Nat.Partition n)).filter
      (fun p => ∀ a ∈ p.parts, a ∈ A),
      (-1 : ℤ) ^ p.parts.card * (p.parts.card : ℤ) ^ k := by
  classical
  unfold S c
  simp_rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    Finset.mul_sum, mul_one, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : ∀ a ∈ p.parts, a ∈ A
  · rw [Finset.sum_eq_single p.parts.card]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · intro h
      exact (h (Finset.mem_range.mpr (by have := parts_card_le p; omega))).elim
  · simp [hp]

private lemma multiset_126 (p : Multiset ℕ) (hp : ∀ a ∈ p, a = 1 ∨ a = 2 ∨ a = 6) :
    p = Multiset.replicate (p.count 1) 1 + Multiset.replicate (p.count 2) 2 +
      Multiset.replicate (p.count 6) 6 := by
  apply Multiset.ext.mpr
  intro a
  by_cases h1 : a = 1
  · subst a; simp [Multiset.count_replicate]
  by_cases h2 : a = 2
  · subst a; simp [Multiset.count_replicate]
  by_cases h6 : a = 6
  · subst a; simp [Multiset.count_replicate]
  have ha : a ∉ p := by intro h; rcases hp a h with h | h | h <;> contradiction
  simp [Multiset.count_replicate, Multiset.count_eq_zero_of_notMem ha, Ne.symm h1, Ne.symm h2, Ne.symm h6]

private def partition126 (n y z : ℕ) (h : 2*y+6*z ≤ n) : Nat.Partition n :=
  Nat.Partition.ofSums n (Multiset.replicate (n - 2*y - 6*z) 1 +
    Multiset.replicate y 2 + Multiset.replicate z 6) (by simp; omega)

private lemma partition126_parts (n y z : ℕ) (h : 2*y+6*z ≤ n) :
    (partition126 n y z h).parts = Multiset.replicate (n - 2*y - 6*z) 1 +
      Multiset.replicate y 2 + Multiset.replicate z 6 := by
  dsimp only [partition126, Nat.Partition.ofSums]
  apply Multiset.filter_eq_self.mpr
  intro a ha
  simp only [Multiset.mem_add, Multiset.mem_replicate] at ha
  rcases ha with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> decide

private lemma partition126_counts (n y z : ℕ) (h : 2*y+6*z ≤ n) :
    (partition126 n y z h).parts.count 2 = y ∧
    (partition126 n y z h).parts.count 6 = z ∧
    (partition126 n y z h).parts.card = n - y - 5*z := by
  simp only [partition126_parts]
  simp [Multiset.count_replicate]
  omega

private lemma partition126_inverse {n : ℕ} (p : Nat.Partition n)
    (hp : ∀ a ∈ p.parts, a ∈ ({1,2,6} : Set ℕ)) :
    ∃ h : 2 * p.parts.count 2 + 6 * p.parts.count 6 ≤ n,
      partition126 n (p.parts.count 2) (p.parts.count 6) h = p := by
  have he := multiset_126 p.parts (by simpa using hp)
  have hs := congrArg Multiset.sum he
  simp only [p.parts_sum, Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul,
    mul_one, Nat.cast_id] at hs
  have hh : 2 * p.parts.count 2 + 6 * p.parts.count 6 ≤ n := by omega
  refine ⟨hh, Nat.Partition.ext ?_⟩
  have hx : n - 2*p.parts.count 2 - 6*p.parts.count 6 = p.parts.count 1 := by omega
  rw [partition126_parts, hx]
  exact he.symm

private lemma S_coordinates (k n : ℕ) :
    S (U 3) k n = ∑ z ∈ Finset.range (n/6+1),
      ∑ y ∈ Finset.range ((n-6*z)/2+1),
        (-1 : ℤ) ^ (n-y-5*z) * ((n-y-5*z : ℕ) : ℤ)^k := by
  classical
  rw [U_three, S_eq_partition_sum, Finset.sum_sigma']
  apply Finset.sum_bij (fun p _ => ⟨p.parts.count 6, p.parts.count 2⟩)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨h, _⟩ := partition126_inverse p hp
    simp only [Finset.mem_sigma, Finset.mem_range]
    omega
  · intro p hp q hq he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨h, hh⟩ := partition126_inverse p hp
    obtain ⟨h', hh'⟩ := partition126_inverse q hq
    have hy : p.parts.count 2 = q.parts.count 2 := congrArg Sigma.snd he
    have hz : p.parts.count 6 = q.parts.count 6 := congrArg Sigma.fst he
    apply Nat.Partition.ext
    rw [← hh, ← hh']
    simp only [partition126_parts]
    simp [hy, hz]
  · intro a ha
    have ha' := Finset.mem_sigma.mp ha
    have hh : 2 * a.2 + 6 * a.1 ≤ n := by
      have hz := Finset.mem_range.mp ha'.1
      have hy := Finset.mem_range.mp ha'.2
      omega
    refine ⟨partition126 n a.2 a.1 hh, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro b hb
      rw [partition126_parts] at hb
      simp only [Multiset.mem_add, Multiset.mem_replicate] at hb
      rcases hb with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> simp
    · obtain ⟨hy, hz, _⟩ := partition126_counts n a.2 a.1 hh
      apply Sigma.ext hz
      simpa using hy
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨h, he⟩ := partition126_inverse p hp
    have hc := (partition126_counts n (p.parts.count 2) (p.parts.count 6) h).2.2
    rw [he] at hc
    simp [hc]

private lemma alternating_quadratic (M : ℕ) (T : ℤ) :
    2 * (∑ y ∈ Finset.range (M+1), (-1 : ℤ)^y * (T - (y : ℤ))^2) =
      T*(T+1) + (-1 : ℤ)^M * (T - (M : ℤ)) * (T - (M : ℤ) - 1) := by
  have h := Finset.sum_range_sub' (fun y : ℕ =>
    (-1:ℤ)^y * (T-(y:ℤ)) * (T-(y:ℤ)+1)) (M+1)
  have he : 2 * (∑ y ∈ Finset.range (M+1), (-1 : ℤ)^y * (T - (y : ℤ))^2) =
      ∑ y ∈ Finset.range (M+1),
        ((-1:ℤ)^y * (T-(y:ℤ)) * (T-(y:ℤ)+1) -
          (-1:ℤ)^(y+1) * (T-((y+1:ℕ):ℤ)) * (T-((y+1:ℕ):ℤ)+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [pow_succ]
    push_cast
    ring
  rw [he, h]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, pow_succ, pow_zero, one_mul]
  ring

private lemma outer_alternating (r : ℕ) (T : ℤ) :
    (∑ z ∈ Finset.range (2*r+1), (-1 : ℤ)^z * (T-5*(z:ℤ))*(T-5*(z:ℤ)+1)) =
      T*(T+1) - 10*T*(r:ℤ) + 50*(r:ℤ)^2 + 20*(r:ℤ) := by
  have h := Finset.sum_range_sub' (fun z : ℕ =>
    (-1:ℤ)^z * (2*(T-5*(z:ℤ))^2+12*(T-5*(z:ℤ))+5)) (2*r+1)
  have he : 4 * (∑ z ∈ Finset.range (2*r+1),
      (-1 : ℤ)^z * (T-5*(z:ℤ))*(T-5*(z:ℤ)+1)) =
      ∑ z ∈ Finset.range (2*r+1),
        ((-1:ℤ)^z * (2*(T-5*(z:ℤ))^2+12*(T-5*(z:ℤ))+5) -
          (-1:ℤ)^(z+1) * (2*(T-5*((z+1:ℕ):ℤ))^2+12*(T-5*((z+1:ℕ):ℤ))+5)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [pow_succ]
    push_cast
    ring
  rw [← he] at h
  norm_num [pow_add, pow_mul, Nat.cast_add, Nat.cast_mul] at h
  have hr : 4 * (T*(T+1) - 10*T*(r:ℤ) + 50*(r:ℤ)^2 + 20*(r:ℤ)) =
      2*T^2+12*T+5 +
        (2*(T-5*(2*(r:ℤ)+1))^2+12*(T-5*(2*(r:ℤ)+1))+5) := by ring
  -- he is the normalized telescope for four times the required sum.
  omega

private lemma outer_ordinary (r : ℕ) (T : ℤ) :
    3 * (∑ z ∈ Finset.range (2*r+1), (T-2*(z:ℤ))*(T-2*(z:ℤ)-1)) =
      (2*(r:ℤ)+1)*(3*T^2-3*T-12*T*(r:ℤ)+16*(r:ℤ)^2+10*(r:ℤ)) := by
  have h1 := sum_range_pow (2*r+1) 1
  have h2 := sum_range_pow (2*r+1) 2
  conv_rhs at h1 => norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli_one]
  conv_rhs at h2 => norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli_one, bernoulli_two]
  simp only [pow_one] at h1
  have hexp :
      (∑ z ∈ Finset.range (2*r+1), ((T:ℚ)-2*(z:ℚ))*((T:ℚ)-2*(z:ℚ)-1)) =
        ((T:ℚ)^2-(T:ℚ))*(2*(r:ℚ)+1) +
          (-4*(T:ℚ)+2)*(∑ z ∈ Finset.range (2*r+1), (z:ℚ)) +
          4*(∑ z ∈ Finset.range (2*r+1), (z:ℚ)^2) := by
    calc
      _ = ∑ z ∈ Finset.range (2*r+1),
        (((T:ℚ)^2-(T:ℚ)) + (-4*(T:ℚ)+2)*(z:ℚ) + 4*(z:ℚ)^2) := by
          apply Finset.sum_congr rfl
          intro z _
          ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        simp
        ring
  have hq :
      3 * (∑ z ∈ Finset.range (2*r+1), ((T:ℚ)-2*(z:ℚ))*((T:ℚ)-2*(z:ℚ)-1)) =
        (2*(r:ℚ)+1)*(3*(T:ℚ)^2-3*(T:ℚ)-12*(T:ℚ)*(r:ℚ)+16*(r:ℚ)^2+10*(r:ℚ)) := by
    rw [hexp, h1, h2]
    push_cast
    ring
  exact_mod_cast hq

private lemma signed_coordinates (r : ℕ) :
    S (U 3) 2 (12*r+2) = ∑ z ∈ Finset.range (2*r+1),
      (-1 : ℤ)^z * ∑ y ∈ Finset.range (6*r+1-3*z+1),
        (-1 : ℤ)^y * (12*(r:ℤ)+2-5*(z:ℤ)-(y:ℤ))^2 := by
  rw [S_coordinates, show (12*r+2)/6 = 2*r by omega]
  apply Finset.sum_congr rfl
  intro z hz
  have hz' := Finset.mem_range.mp hz
  rw [show (12*r+2-6*z)/2 = 6*r+1-3*z by omega, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  have hy' := Finset.mem_range.mp hy
  have hp : (-1 : ℤ)^(12*r+2-y-5*z) = (-1 : ℤ)^z * (-1 : ℤ)^y := by
    rw [← pow_add]
    apply neg_one_pow_congr
    simp only [Nat.even_iff]
    omega
  have hc : ((12*r+2-y-5*z : ℕ):ℤ) = 12*(r:ℤ)+2-5*(z:ℤ)-(y:ℤ) := by omega
  rw [hp, hc]
  ring

private lemma double_sum (r : ℕ) :
    2*S (U 3) 2 (12*r+2) =
      (∑ z ∈ Finset.range (2*r+1), (-1:ℤ)^z *
        (12*(r:ℤ)+2-5*(z:ℤ))*(12*(r:ℤ)+3-5*(z:ℤ))) -
      (∑ z ∈ Finset.range (2*r+1),
        (6*(r:ℤ)+1-2*(z:ℤ))*(6*(r:ℤ)-2*(z:ℤ))) := by
  rw [signed_coordinates, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  have hz' := Finset.mem_range.mp hz
  have hm : ((6*r+1-3*z:ℕ):ℤ) = 6*(r:ℤ)+1-3*(z:ℤ) := by omega
  have hsgn : (-1:ℤ)^z * (-1:ℤ)^(6*r+1-3*z) = -1 := by
    rw [← pow_add]
    apply Odd.neg_one_pow
    rw [Nat.odd_iff]
    omega
  calc
    _ = (-1:ℤ)^z * (2 * ∑ y ∈ Finset.range (6*r+1-3*z+1),
        (-1:ℤ)^y * (12*(r:ℤ)+2-5*(z:ℤ)-(y:ℤ))^2) := by ring
    _ = _ := by
      rw [alternating_quadratic]
      simp only [mul_add, ← mul_assoc]
      rw [hsgn, hm]
      ring

private lemma cubic (r : ℕ) :
    S (U 3) 2 (12*r+2)*3 = -52*(r:ℤ)^3+69*(r:ℤ)^2+82*(r:ℤ)+9 := by
  have hd := double_sum r
  have ha := outer_alternating r (12*(r:ℤ)+2)
  have hb := outer_ordinary r (6*(r:ℤ)+1)
  have ha' : (∑ z ∈ Finset.range (2*r+1), (-1:ℤ)^z *
      (12*(r:ℤ)+2-5*(z:ℤ))*(12*(r:ℤ)+3-5*(z:ℤ))) =
      74*(r:ℤ)^2+60*(r:ℤ)+6 := by
    calc
      _ = ∑ z ∈ Finset.range (2*r+1), (-1:ℤ)^z *
          (12*(r:ℤ)+2-5*(z:ℤ))*((12*(r:ℤ)+2)-5*(z:ℤ)+1) := by
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by rw [ha]; ring
  have hb' : 3*(∑ z ∈ Finset.range (2*r+1),
      (6*(r:ℤ)+1-2*(z:ℤ))*(6*(r:ℤ)-2*(z:ℤ))) =
      104*(r:ℤ)^3+84*(r:ℤ)^2+16*(r:ℤ) := by
    calc
      _ = 3*(∑ z ∈ Finset.range (2*r+1),
          ((6*(r:ℤ)+1)-2*(z:ℤ))*((6*(r:ℤ)+1)-2*(z:ℤ)-1)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by rw [hb]; ring
  omega

private lemma negative_family (s : ℕ) : S (U 3) 2 (12*s+38) < 0 := by
  have hc := cubic (s+3)
  rw [show 12*(s+3)+2 = 12*s+38 by omega] at hc
  have hs : 0 ≤ (s:ℤ) := Int.natCast_nonneg s
  push_cast at hc
  nlinarith [sq_nonneg (s:ℤ), pow_nonneg hs 3]

theorem result : ¬ claim := by
  intro h
  obtain ⟨N, hN⟩ := (h 3 (by decide)).2 2 (by decide)
  have hn := hN (12*N+38) (by omega)
  have he : Even (12*N+38) := ⟨6*N+19, by omega⟩
  rw [he.neg_one_pow, one_mul] at hn
  have hneg := negative_family N
  omega


end D5.S1.Recurrence.Partitions.GawronUlasFactorialSignConjecture
