/- GID: D5/S3/Arith/GoelPisanoRatioRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/GoelPisanoRatioRefutation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Goel's prime-domain Pisano-rank ratios omit five and every multiple of five. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#13841; Refuted)
Direct frozen dependencies:
  D5/S3/Arith/FibonacciAtomic/TimeSampling.prime_zero_rank_facts
    statement_id: sha256:9abb2390abb56faf4c6d65cee8b83e7d10788bca72e9b91f7538a0b4c80c2d37
  D5/S3/Arith/FibonacciAtomic/TimeSampling.zeroRank
    statement_id: sha256:ca05113843898a6129d0b704dfcd7d072406644168d68db4ef00214dae89c0b0
  D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.step
    statement_id: sha256:abd1497f7c6dd19d79eb07033d7697ada8db81677041e77acfe8c3b896948d5d
  D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.iterate_first
    statement_id: sha256:dbfb5a99b51a348e94beb8e1a7c4bd9e694acb181796d294e801faff35efe568
  D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.iterate_second
    statement_id: sha256:2aaac89f149ef12a686b5914674eef427a34f57f335f442e548c78e2d6e62ca6
  D5/S3/Arith/FibonacciRank.fibonacci_rank_dvd_prime_bound
    statement_id: sha256:3b3f6fd70742a99dee370aea0221e64bc1c3c84e8c242d8707542778f181893c
  D5/S3/Arith/GoldenApparition.fibonacci_apparition_entry_point
    statement_id: sha256:78d0346c819f9913279ef688be6a8cc41b2e4f1507b0b156d064dc542b2f6f90
Private auxiliary declarations (no independent escape witness):
  iterate_fib: proof_shape: bind-only; consumers: period_iff_return
  period_iff_return: proof_shape: bind-only; consumers: pi_eq_minimalPeriod, pi_dvd_of_period
  pi_eq_minimalPeriod: proof_shape: bind-only; consumers: pi_dvd_of_period
  pi_dvd_of_period: proof_shape: bind-only; consumers: pi_dvd_split
  epsilon_cases: proof_shape: bind-only
    consumers: pi_dvd_square_sub_one, epsilon_p_negative, epsilon_q_negative
  pair_shift: proof_shape: bind-only; consumers: period_of_pair, double_period_of_negative_pair
  period_of_pair: proof_shape: bind-only; consumers: pi_dvd_split
  double_period_of_negative_pair: proof_shape: bind-only; consumers: pi_dvd_split
  apparition_cast: proof_shape: bind-only; consumers: pi_dvd_split
  pi_dvd_split: proof_shape: bind-only
    consumers: pi_dvd_square_sub_one, epsilon_q_negative, five_not_dvd_pi
  pi_dvd_square_sub_one: proof_shape: bind-only; consumers: epsilon_p_negative
  z_dvd_prime_bound: proof_shape: bind-only; consumers: epsilon_p_negative, epsilon_q_negative
  z_ge_five: proof_shape: bind-only; consumers: epsilon_p_negative, epsilon_q_negative
  epsilon_p_negative: proof_shape: bind-only; consumers: epsilon_q_negative
  epsilon_q_negative: proof_shape: bind-only; consumers: five_not_dvd_pi
  epsilon_negative_residues: proof_shape: bind-only; consumers: five_not_dvd_pi
  five_not_dvd_pi: proof_shape: bind-only; consumers: ratio_avoids_five
  ratio_avoids_five: proof_shape: bind-only; consumers: result
Computational content: none; the argument is symbolic and uniform in all eligible primes.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Arith.FibonacciAtomic.TimeSampling
import D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.GoelPisanoRatioRefutation

open D5.S3.Arith.FibonacciAtomic.TimeSampling (zeroRank)
open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step)

/-- The least positive period of the Fibonacci residues, using natural-number infimum. -/
noncomputable def pisanoPeriod (n : ℕ) : ℕ :=
  sInf {k | 0 < k ∧ ∀ m, Nat.fib (m + k) % n = Nat.fib m % n}

/-- A Sophie Germain prime and its associated prime. -/
def SophieGermain (q : ℕ) : Prop := q.Prime ∧ (2 * q + 1).Prime

/-- Goel's OQ4, with the source's standing prime domain and positive odd values.
The source's z is the existing, literally identical `TimeSampling.zeroRank`. -/
def claim : Prop :=
  {R : ℕ | ∃ q, q.Prime ∧ (2 * q + 1).Prime ∧ 5 < q ∧
    zeroRank (2 * q + 1) ∣ pisanoPeriod q ∧ R = pisanoPeriod q / zeroRank (2 * q + 1)} = {R : ℕ | Odd R}

attribute [local instance] D5.S3.Arith.FibonacciRank.instFactPrimeOfNatNat_d5

private theorem iterate_fib (n k : ℕ) :
    (step (A := ZMod n))^[k] (0, 1) =
      ((Nat.fib k : ZMod n), (Nat.fib (k + 1) : ZMod n)) := by
  cases k with
  | zero => simp
  | succ k =>
    apply Prod.ext
    · simpa using
        D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling.iterate_first
          (k + 1) (Nat.succ_pos k) ((0, 1) : ZMod n × ZMod n)
    · simpa using
        D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling.iterate_second
          (k + 1) ((0, 1) : ZMod n × ZMod n)

private theorem period_iff_return (n k : ℕ) :
    (∀ m, Nat.fib (m + k) % n = Nat.fib m % n) ↔
      Function.IsPeriodicPt (step (A := ZMod n)) k (0, 1) := by
  constructor
  · intro h
    change (step (A := ZMod n))^[k] (0, 1) = (0, 1)
    rw [iterate_fib]
    apply Prod.ext
    · have h0 := h 0
      simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h0
    · have h1 := h 1
      simpa [Nat.add_comm] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
  · intro h m
    have hm : (step (A := ZMod n))^[m + k] (0, 1) =
        (step (A := ZMod n))^[m] (0, 1) := by
      rw [Function.iterate_add_apply, h.eq]
    have hh := congrArg Prod.fst hm
    rw [iterate_fib, iterate_fib] at hh
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hh

private theorem pi_eq_minimalPeriod (n : ℕ) :
    pisanoPeriod n = Function.minimalPeriod (step (A := ZMod n)) (0, 1) := by
  rw [Function.minimalPeriod_eq_sInf_n_pos_IsPeriodicPt]
  unfold pisanoPeriod
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq, period_iff_return]

private theorem pi_dvd_of_period {n k : ℕ}
    (h : ∀ m, Nat.fib (m + k) % n = Nat.fib m % n) : pisanoPeriod n ∣ k := by
  rw [pi_eq_minimalPeriod]
  exact (Function.isPeriodicPt_iff_minimalPeriod_dvd).mp ((period_iff_return n k).mp h)

private theorem epsilon_cases {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) :
    legendreSym 5 p = 1 ∨ legendreSym 5 p = -1 := by
  apply legendreSym.eq_one_or_neg_one
  rw [Int.cast_natCast, ne_eq, ZMod.natCast_eq_zero_iff]
  intro h
  exact hp5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp h).symm

private theorem pair_shift {n k : ℕ} {c : ZMod n}
    (h0 : (Nat.fib k : ZMod n) = 0) (h1 : (Nat.fib (k + 1) : ZMod n) = c)
    (m : ℕ) : (Nat.fib (m + k) : ZMod n) = c * (Nat.fib m : ZMod n) := by
  cases m with
  | zero => simpa using h0
  | succ m =>
    have h := congrArg (fun t : ℕ => (t : ZMod n)) (Nat.fib_add k m)
    simpa [Nat.cast_add, Nat.cast_mul, h0, h1, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using h

private theorem period_of_pair {n k : ℕ}
    (h0 : (Nat.fib k : ZMod n) = 0) (h1 : (Nat.fib (k + 1) : ZMod n) = 1) :
    ∀ m, Nat.fib (m + k) % n = Nat.fib m % n := by
  intro m
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
  simpa using pair_shift h0 h1 m

private theorem double_period_of_negative_pair {n k : ℕ}
    (h0 : (Nat.fib k : ZMod n) = 0) (h1 : (Nat.fib (k + 1) : ZMod n) = -1) :
    ∀ m, Nat.fib (m + 2 * k) % n = Nat.fib m % n := by
  intro m
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
  rw [show m + 2 * k = (m + k) + k by omega,
    pair_shift h0 h1, pair_shift h0 h1]
  ring

private theorem apparition_cast {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) :
    (Int.fib ((p : ℤ) - legendreSym 5 p) : ZMod p) = 0 ∧
      (Nat.fib p : ZMod p) = (legendreSym 5 p : ZMod p) := by
  have hnot : ¬ p ∣ 5 := fun h => hp5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h)
  simpa [Int.fib_natCast] using
    D5.S3.Arith.GoldenApparition.fibonacci_apparition_entry_point hp hnot

private theorem pi_dvd_split {q : ℕ} (hq : q.Prime) (hq5 : q ≠ 5) :
    (legendreSym 5 q = 1 → pisanoPeriod q ∣ q - 1) ∧ (legendreSym 5 q = -1 → pisanoPeriod q ∣ 2 * (q + 1)) := by
  obtain ⟨h0, hqfib⟩ := apparition_cast hq hq5
  have hqle := hq.one_le
  constructor
  · intro he
    have hi : (q : ℤ) - legendreSym 5 q = ((q - 1 : ℕ) : ℤ) := by rw [he]; omega
    rw [hi, Int.fib_natCast, Int.cast_natCast] at h0
    have h1 : (Nat.fib ((q - 1) + 1) : ZMod q) = 1 := by
      rw [Nat.sub_add_cancel hq.one_le]
      simpa [he] using hqfib
    exact pi_dvd_of_period (period_of_pair h0 h1)
  · intro he
    have hi : (q : ℤ) - legendreSym 5 q = ((q + 1 : ℕ) : ℤ) := by rw [he]; omega
    rw [hi, Int.fib_natCast, Int.cast_natCast] at h0
    have h1 : (Nat.fib ((q + 1) + 1) : ZMod q) = -1 := by
      rw [show q + 1 + 1 = q + 2 by omega, Nat.fib_add_two, Nat.cast_add, h0]
      simpa [he] using hqfib
    exact pi_dvd_of_period (double_period_of_negative_pair h0 h1)

private theorem pi_dvd_square_sub_one {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq5 : q ≠ 5) :
    pisanoPeriod q ∣ q ^ 2 - 1 := by
  have hfact : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have := Nat.sub_add_cancel hq.one_le
    have : q ^ 2 ≥ 1 := by nlinarith [hq.two_le]
    have := Nat.sub_add_cancel this
    nlinarith
  rw [hfact]
  rcases epsilon_cases hq hq5 with he | he
  · exact dvd_mul_of_dvd_left ((pi_dvd_split hq hq5).1 he) (q + 1)
  · apply dvd_trans ((pi_dvd_split hq hq5).2 he)
    obtain ⟨a, ha⟩ := hq.odd_of_ne_two hq2
    refine ⟨a, ?_⟩
    have hsub : q - 1 = 2 * a := by omega
    rw [hsub]
    ring

private theorem z_dvd_prime_bound {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) :
    zeroRank p ∣ if legendreSym 5 p = 1 then p - 1 else p + 1 := by
  obtain ⟨hpos, hzero, hmin⟩ := D5.S3.Arith.FibonacciAtomic.TimeSampling.prime_zero_rank_facts p hp
  exact D5.S3.Arith.FibonacciRank.fibonacci_rank_dvd_prime_bound hp hp5 hpos hzero hmin

private theorem z_ge_five {p : ℕ} (hprime : p.Prime) (hp : 11 < p) : 5 ≤ zeroRank p := by
  obtain ⟨hpos, hzero, _⟩ := D5.S3.Arith.FibonacciAtomic.TimeSampling.prime_zero_rank_facts p hprime
  by_contra h
  have hfpos : 0 < Nat.fib (zeroRank p) := Nat.fib_pos.mpr hpos
  have hp_le := Nat.le_of_dvd hfpos hzero
  have hf_le := Nat.fib_mono (show zeroRank p ≤ 4 by omega)
  norm_num at hf_le
  omega

private theorem epsilon_p_negative {q : ℕ} (hq : q.Prime) (hp : (2 * q + 1).Prime)
    (hqgt : 5 < q) (hzpi : zeroRank (2 * q + 1) ∣ pisanoPeriod q) : legendreSym 5 (2 * q + 1 : ℕ) = -1 := by
  rcases epsilon_cases hp (by omega) with he | he
  · have hrank := z_dvd_prime_bound hp (by omega)
    rw [if_pos he] at hrank
    have h2q : zeroRank (2 * q + 1) ∣ 2 * q := by simpa using hrank
    have hsq : zeroRank (2 * q + 1) ∣ q ^ 2 - 1 :=
      dvd_trans hzpi (pi_dvd_square_sub_one hq (by omega) (by omega))
    have hspos : 1 ≤ q ^ 2 := by nlinarith [hq.two_le]
    have hcSq : (q ^ 2).Coprime (q ^ 2 - 1) :=
      (Nat.coprime_self_sub_right hspos).mpr (Nat.coprime_one_right _)
    have hqSq : q ∣ q ^ 2 := ⟨q, by ring⟩
    have hc := Nat.Coprime.of_dvd_right hsq (Nat.Coprime.of_dvd_left hqSq hcSq)
    have hz2 : zeroRank (2 * q + 1) ∣ 2 := hc.symm.dvd_of_dvd_mul_right h2q
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hz2
    have hge := z_ge_five hp (show 11 < 2 * q + 1 by omega)
    omega
  · exact he

private theorem epsilon_q_negative {q : ℕ} (hq : q.Prime) (hp : (2 * q + 1).Prime)
    (hqgt : 5 < q) (hzpi : zeroRank (2 * q + 1) ∣ pisanoPeriod q) : legendreSym 5 q = -1 := by
  have hep := epsilon_p_negative hq hp hqgt hzpi
  have hrank := z_dvd_prime_bound hp (by omega)
  have hnot : legendreSym 5 (2 * q + 1 : ℕ) ≠ 1 := by omega
  rw [if_neg hnot] at hrank
  have h2plus : zeroRank (2 * q + 1) ∣ 2 * (q + 1) := by
    convert hrank using 1 <;> ring
  rcases epsilon_cases hq (by omega) with he | he
  · have hminus : zeroRank (2 * q + 1) ∣ q - 1 :=
      dvd_trans hzpi ((pi_dvd_split hq (by omega)).1 he)
    have h2minus : zeroRank (2 * q + 1) ∣ 2 * (q - 1) := dvd_mul_of_dvd_right hminus 2
    have h4 : zeroRank (2 * q + 1) ∣ 4 := by
      have hdiff : 2 * (q + 1) - 2 * (q - 1) = 4 := by omega
      simpa [hdiff] using Nat.dvd_sub h2plus h2minus
    have hle := Nat.le_of_dvd (by norm_num : 0 < 4) h4
    have hge := z_ge_five hp (show 11 < 2 * q + 1 by omega)
    omega
  · exact he

private theorem epsilon_negative_residues {q : ℕ} (he : legendreSym 5 q = -1) :
    q % 5 = 2 ∨ q % 5 = 3 := by
  have hns : ¬ IsSquare (q : ZMod 5) := (legendreSym.eq_neg_one_iff' (p := 5)).mp he
  have hcast : (q : ZMod 5) = ((q % 5 : ℕ) : ZMod 5) := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
    simp
  have hm := Nat.mod_lt q (by norm_num : 0 < 5)
  by_contra h
  have hor : q % 5 = 0 ∨ q % 5 = 1 ∨ q % 5 = 4 := by omega
  apply hns
  rcases hor with h0 | h1 | h4
  · rw [hcast, h0]
    exact ⟨0, by norm_num⟩
  · rw [hcast, h1]
    exact ⟨1, by norm_num⟩
  · rw [hcast, h4]
    exact ⟨2, by norm_num⟩

private theorem five_not_dvd_pi {q : ℕ} (hq : q.Prime) (hp : (2 * q + 1).Prime)
    (hqgt : 5 < q) (hzpi : zeroRank (2 * q + 1) ∣ pisanoPeriod q) : ¬ 5 ∣ pisanoPeriod q := by
  have he := epsilon_q_negative hq hp hqgt hzpi
  have hbound := (pi_dvd_split hq (by omega)).2 he
  have hres := epsilon_negative_residues he
  intro h5
  have hd : 5 ∣ 2 * (q + 1) := dvd_trans h5 hbound
  have hm : (2 * (q + 1)) % 5 = 0 := Nat.mod_eq_zero_of_dvd hd
  omega

private theorem ratio_avoids_five {q : ℕ} (hsg : SophieGermain q)
    (hqgt : 5 < q) (hzpi : zeroRank (2 * q + 1) ∣ pisanoPeriod q) : ¬ 5 ∣ pisanoPeriod q / zeroRank (2 * q + 1) := by
  intro h
  exact five_not_dvd_pi hsg.1 hsg.2 hqgt hzpi (dvd_trans h (Nat.div_dvd_of_dvd hzpi))

theorem result : ¬ claim := by
  intro hclaim
  have hodd : Odd (5 : ℕ) := by decide
  have hmem : (5 : ℕ) ∈ {R : ℕ | ∃ q, q.Prime ∧ (2 * q + 1).Prime ∧ 5 < q ∧
      zeroRank (2 * q + 1) ∣ pisanoPeriod q ∧ R = pisanoPeriod q / zeroRank (2 * q + 1)} := by
    rw [hclaim]
    exact hodd
  obtain ⟨q, hq, hp, hgt, hz, hr⟩ := hmem
  apply ratio_avoids_five ⟨hq, hp⟩ hgt hz
  rw [← hr]


end D5.S3.Arith.GoelPisanoRatioRefutation
