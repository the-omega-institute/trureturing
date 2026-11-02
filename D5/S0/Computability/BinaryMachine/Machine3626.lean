/- GID: D5/S0/Computability/BinaryMachine/Machine3626
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/Machine3626
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Moebius, mathlib/module/Mathlib.Data.Nat.Totient]
   utility: none
   digest: The signed Moebius divisor sum counts actual transitions of machine 3626. -/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Nat.Totient

/-!
# Exact halting formula for the one-sided two-state machine

Admission basis: open-problem-resolution, preregistered issue #25808.
The arithmetic prime-power identities are literature-attested in A069517.
They are consumed here, rather than delivered as separate known results.

Proof shapes and live consumers (same-delivery helpers are inlined):
* trace_trans: content; consumed by block_trace.
* block_trace: content; restoring recursion consumed by block_first_crossing.
* block_first_crossing: content; consumed by positive_input_first_crossing.
* positive_input_first_crossing: content; consumed by result.
* signedMu_mult: bind-only; consumed by mass_mult.
* mass_mult: bind-only; consumed by cost_mult, cost_two_pow, cost_odd_prime_pow.
* cost_mult: bind-only; consumed by cost_odd and cost_binary_block.
* mass_prime_pow: bind-only; consumed by cost_two_pow and cost_odd_prime_pow.
* cost_two_pow: bind-only; consumed by cost_binary_block.
* cost_odd_prime_pow: bind-only; consumed by cost_odd.
* cost_odd: bind-only; consumed by cost_binary_block.
* cost_binary_block: bind-only; consumed by result.
* block_prefix_unique: bind-only; consumed by result.
* result: content through the live restoring trace; settling result.
All direct frozen D5 dependencies are absent; pinned Mathlib is used directly.
No arithmetic helper supplies an independent escape witness.
-/

set_option autoImplicit false

@[expose] public section

namespace D5.S0.Computability.BinaryMachine.Machine3626

inductive State
  | A | B

/-- The left list starts at the scanned cell; absent cells are blank zero.
The right list ends at the fixed right boundary. Both lists have unbounded length. -/
structure Cfg where
  state : State
  left : List Bool
  right : List Bool

/-- Write at the current cell and move one cell right; crossing the boundary halts. -/
def exitRight (writtenLeft right : List Bool) : Option Cfg :=
  match right with
  | [] => none
  | b :: rest => some ⟨.B, b :: writtenLeft, rest⟩

/-- Each application is one simultaneous read/write/state-change/move transition.
The two empty-left cases read an implicit blank cell on the infinite half-tape. -/
def step : Cfg → Option Cfg
  | ⟨.A, [], right⟩ => some ⟨.A, [], false :: right⟩
  | ⟨.A, false :: left, right⟩ => some ⟨.A, left, false :: right⟩
  | ⟨.A, true :: left, right⟩ => exitRight (true :: left) right
  | ⟨.B, [], right⟩ => some ⟨.A, [], true :: right⟩
  | ⟨.B, false :: left, right⟩ => some ⟨.A, left, true :: right⟩
  | ⟨.B, true :: left, right⟩ => exitRight (false :: left) right

/-- A trace may stop at its current configuration or at the first boundary crossing.
There is no constructor that continues after a crossing; the crossing counts one step. -/
inductive Trace : ℕ → Cfg → Option Cfg → Prop
  | zero (c : Cfg) : Trace 0 c (some c)
  | cons {t : ℕ} {c d : Cfg} {result : Option Cfg}
      (transition : step c = some d) (rest : Trace t d result) :
      Trace (t + 1) c result
  | crossing {c : Cfg} (transition : step c = none) : Trace 1 c none

private theorem trace_trans {s t : ℕ} {c : Cfg} {endpoint result : Option Cfg}
    (h : Trace s c endpoint) :
    ∀ {d : Cfg}, endpoint = some d → Trace t d result → Trace (s + t) c result := by
  induction h with
  | zero c =>
    intro d he j
    cases he
    simpa using j
  | cons transition rest ih =>
    intro d he j
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Trace.cons transition (ih he j)
  | crossing transition =>
    intro d he
    cases he

/-- A zero block followed by its first one and arbitrary higher cells. -/
def block (k : ℕ) (higher : List Bool) : List Bool :=
  List.replicate k false ++ true :: higher

private def blockTime : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * blockTime k + 3

private theorem block_trace (k : ℕ) (higher right : List Bool) :
    Trace (blockTime k) ⟨.A, block k higher, right⟩
      (exitRight (block k higher) right) := by
  induction k generalizing right with
  | zero =>
    cases right with
    | nil => exact Trace.crossing rfl
    | cons b rest => exact Trace.cons rfl (Trace.zero _)
  | succ k ih =>
    have hleft : Trace (blockTime k) ⟨.A, block k higher, false :: right⟩
        (some ⟨.B, false :: block k higher, right⟩) := by
      simpa [exitRight] using ih (false :: right)
    have hright : Trace (blockTime k) ⟨.A, block k higher, true :: right⟩
        (some ⟨.B, true :: block k higher, right⟩) := by
      simpa [exitRight] using ih (true :: right)
    have hlast : Trace 1 ⟨.B, true :: block k higher, right⟩
        (exitRight (false :: block k higher) right) := by
      cases right with
      | nil => exact Trace.crossing rfl
      | cons b rest => exact Trace.cons rfl (Trace.zero _)
    have hmiddle := trace_trans hleft rfl
      (Trace.cons (by rfl) (trace_trans hright rfl hlast))
    have hfull := Trace.cons (c := ⟨.A, false :: block k higher, right⟩)
      (by rfl) hmiddle
    simpa [blockTime, block, List.replicate_succ, Nat.two_mul, Nat.add_assoc] using hfull

/-- Every zero block followed by one crosses the actual right boundary for the first time
in exactly the stated number of transitions, independently of all higher cells. -/
theorem block_first_crossing (k : ℕ) (higher : List Bool) :
    Trace (4 * 2 ^ k - 3) ⟨.A, block k higher, []⟩ none := by
  have htime : ∀ j, blockTime j + 3 = 4 * 2 ^ j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => simp only [blockTime, Nat.pow_succ]; omega
  have ht : blockTime k = 4 * 2 ^ k - 3 := by have := htime k; omega
  simpa only [ht, exitRight] using block_trace k higher []

/-- Binary input is least-significant-bit first, with the head at the right edge. -/
def initial (n : ℕ) : Cfg := ⟨.A, n.bits, []⟩

/-- Every positive binary input has a first one. Its distance from the edge determines
an actual first-crossing trace, with no bound on the input or the tape. -/
theorem positive_input_first_crossing (n : ℕ) (hn : 0 < n) :
    ∃ (k : ℕ) (higher : List Bool), n.bits = block k higher ∧
      Trace (4 * 2 ^ k - 3) (initial n) none := by
  have hshape : ∀ m : ℕ, m ≠ 0 → ∃ (k : ℕ) (higher : List Bool),
      m.bits = block k higher := by
    intro m
    induction m using Nat.binaryRec' with
    | zero =>
      intro h
      exact (h rfl).elim
    | bit b m hb ih =>
      intro hm
      cases b with
      | true =>
        exact ⟨0, m.bits, by simp [block]⟩
      | false =>
        have hm0 : m ≠ 0 := by
          intro h
          simpa using hb h
        obtain ⟨k, higher, hk⟩ := ih hm0
        refine ⟨k + 1, higher, ?_⟩
        rw [Nat.bits_append_bit m false hb, hk]
        simp [block, List.replicate_succ]
  obtain ⟨k, higher, hk⟩ := hshape n (Nat.ne_of_gt hn)
  refine ⟨k, higher, hk, ?_⟩
  simpa only [initial, hk] using block_first_crossing k higher

open scoped ArithmeticFunction.zeta BigOperators
open ArithmeticFunction

private def signedMu : ArithmeticFunction ℤ :=
  ⟨fun n => (-1 : ℤ) ^ (n + 1) * moebius n, by simp⟩

private def mass : ArithmeticFunction ℤ := (ζ : ArithmeticFunction ℤ) * signedMu

private def tot : ArithmeticFunction ℤ :=
  ⟨fun n => (Nat.totient n : ℤ), by simp⟩

private def cost : ArithmeticFunction ℤ :=
  (ζ : ArithmeticFunction ℤ) * ((mass.ppow 2).pmul tot)

private theorem signedMu_mult : signedMu.IsMultiplicative := by
  refine ⟨by norm_num [signedMu], ?_⟩
  intro a b hab
  change (-1 : ℤ) ^ (a * b + 1) * moebius (a * b) =
    ((-1 : ℤ) ^ (a + 1) * moebius a) * ((-1 : ℤ) ^ (b + 1) * moebius b)
  rw [isMultiplicative_moebius.map_mul_of_coprime hab]
  have hp : (-1 : ℤ) ^ (a * b + 1) = (-1 : ℤ) ^ (a + 1) * (-1 : ℤ) ^ (b + 1) := by
    have hnot : ¬ (2 ∣ a ∧ 2 ∣ b) := by
      rintro ⟨ha, hb⟩
      have := Nat.dvd_gcd ha hb
      rw [hab.gcd_eq_one] at this
      norm_num at this
    rw [neg_one_pow_eq_pow_mod_two (a * b + 1),
      neg_one_pow_eq_pow_mod_two (a + 1), neg_one_pow_eq_pow_mod_two (b + 1)]
    have ha := Nat.mod_lt a (by omega : 0 < 2)
    have hb := Nat.mod_lt b (by omega : 0 < 2)
    simp only [Nat.dvd_iff_mod_eq_zero] at hnot
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
      simp [Nat.add_mod, Nat.mul_mod, ha, hb] at *
  rw [hp]
  ring

private theorem mass_mult : mass.IsMultiplicative :=
  isMultiplicative_zeta.natCast.mul signedMu_mult

private theorem cost_mult : cost.IsMultiplicative :=
  isMultiplicative_zeta.natCast.mul
    ((mass_mult.ppow).pmul ⟨by simp [tot], by
      intro a b hab
      change (Nat.totient (a * b) : ℤ) = (Nat.totient a : ℤ) * Nat.totient b
      rw [Nat.totient_mul hab, Nat.cast_mul]⟩)

private theorem mass_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    mass (p ^ k) = 1 - (-1 : ℤ) ^ (p + 1) := by
  rw [mass, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  rw [Finset.sum_range_succ']
  simp only [pow_zero]
  have hterm : ∀ j : ℕ, signedMu (p ^ (j + 1)) =
      if j = 0 then -(-1 : ℤ) ^ (p + 1) else 0 := by
    intro j
    simp only [signedMu, ArithmeticFunction.coe_mk,
      moebius_apply_prime_pow hp (by omega : j + 1 ≠ 0)]
    by_cases hj : j = 0
    · simp [hj]
    · simp [hj]
  simp_rw [hterm]
  simp [signedMu, Finset.sum_ite_eq', hk, sub_eq_add_neg, add_comm]

private theorem cost_two_pow (k : ℕ) : cost (2 ^ k) = 4 * (2 : ℤ) ^ k - 3 := by
  have ht := congrArg (fun x : ℕ => (x : ℤ)) (Nat.sum_totient (2 ^ k))
  rw [Nat.sum_divisors_prime_pow Nat.prime_two, Finset.sum_range_succ'] at ht
  push_cast at ht
  rw [cost, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow Nat.prime_two,
    Finset.sum_range_succ']
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.ppow_apply (by norm_num : 0 < 2)]
  simp_rw [mass_prime_pow 2 _ Nat.prime_two (Nat.succ_pos _)]
  norm_num [tot, mass_mult.map_one] at *
  rw [← Finset.mul_sum]
  linarith

private theorem cost_odd_prime_pow (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    cost (p ^ k) = 1 := by
  have hs : (-1 : ℤ) ^ (p + 1) = 1 := by
    exact (hp.odd_of_ne_two hp2).add_one.neg_one_pow
  rw [cost, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ']
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.ppow_apply (by norm_num : 0 < 2)]
  simp_rw [mass_prime_pow p _ hp (Nat.succ_pos _), hs]
  simp [tot, mass_mult.map_one]

private theorem cost_odd (n : ℕ) (hn : Odd n) : cost n = 1 := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp at hn
  | prime_pow p k hp =>
    by_cases hk : k = 0
    · simp [hk, cost_mult.map_one]
    have hp2 : p ≠ 2 := by
      intro h
      subst p
      have hd : 2 ∣ 2 ^ k := dvd_pow_self 2 hk
      have ho := hn
      rw [Nat.odd_iff] at ho
      have hz := Nat.mod_eq_zero_of_dvd hd
      omega
    exact cost_odd_prime_pow p k hp hp2
  | coprime a b ha hb hab iha ihb =>
    rw [cost_mult.map_mul_of_coprime hab, iha (Nat.odd_mul.mp hn).1,
      ihb (Nat.odd_mul.mp hn).2, one_mul]

private theorem cost_binary_block (n : ℕ) (hn : 0 < n) :
    ∃ (k : ℕ) (higher : List Bool), n.bits = block k higher ∧
      cost n = 4 * (2 : ℤ) ^ k - 3 := by
  have hshape : ∀ m : ℕ, m ≠ 0 → ∃ (k q : ℕ),
      Odd q ∧ m = 2 ^ k * q ∧ m.bits = block k ((q / 2).bits) := by
    intro m
    induction m using Nat.binaryRec' with
    | zero => intro h; exact (h rfl).elim
    | bit b m hb ih =>
      intro hm
      cases b with
      | true =>
        refine ⟨0, 2 * m + 1, ⟨m, by omega⟩, by simp [Nat.bit], ?_⟩
        simp [Nat.bit, block, show (2 * m + 1) / 2 = m by omega]
      | false =>
        have hm0 : m ≠ 0 := by intro h; simpa using hb h
        obtain ⟨k, q, hq, he, hs⟩ := ih hm0
        refine ⟨k + 1, q, hq, ?_, ?_⟩
        · change 2 * m = 2 ^ (k + 1) * q
          rw [he, Nat.pow_succ]
          ring
        · rw [Nat.bits_append_bit m false hb, hs]
          simp [block, List.replicate_succ]
  obtain ⟨k, q, hq, he, hs⟩ := hshape n (Nat.ne_of_gt hn)
  refine ⟨k, (q / 2).bits, hs, ?_⟩
  rw [he, cost_mult.map_mul_of_coprime (hq.coprime_two_left.pow_left k), cost_odd q hq,
    mul_one, cost_two_pow]

private theorem block_prefix_unique (k l : ℕ) (higher rest : List Bool)
    (h : block k higher = block l rest) : k = l := by
  induction k generalizing l with
  | zero =>
    cases l with
    | zero => rfl
    | succ l => simp [block, List.replicate_succ] at h
  | succ k ih =>
    cases l with
    | zero => simp [block, List.replicate_succ] at h
    | succ l =>
      have he : block k higher = block l rest := by
        simpa [block, List.replicate_succ] using h
      exact congrArg Nat.succ (ih l he)

/-- The exact registered signed-Moebius/totient formula counts actual transitions,
including the first move across the fixed right boundary, for every positive input. -/
theorem result (n : ℕ) (hn : 0 < n) :
    ∃ t : ℕ, Trace t (initial n) none ∧
      (t : ℤ) = ∑ d ∈ n.divisors,
        (∑ e ∈ d.divisors, (-1 : ℤ) ^ (e + 1) * moebius e) ^ 2 * (Nat.totient d : ℤ) := by
  obtain ⟨k, higher, hs, ht⟩ := positive_input_first_crossing n hn
  obtain ⟨l, rest, hl, hc⟩ := cost_binary_block n hn
  have hkl := block_prefix_unique k l higher rest (hs.symm.trans hl)
  subst l
  refine ⟨4 * 2 ^ k - 3, ht, ?_⟩
  have hpow : 3 ≤ 4 * 2 ^ k := by have := Nat.one_le_pow k 2 (by omega); omega
  have he : ((4 * 2 ^ k - 3 : ℕ) : ℤ) = cost n := by
    rw [Nat.cast_sub hpow, Nat.cast_mul, Nat.cast_pow, hc]
    norm_num
  rw [he, cost, coe_zeta_mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.ppow_apply (by norm_num : 0 < 2),
    mass, coe_zeta_mul_apply]
  rfl

#print axioms block_first_crossing
#print axioms positive_input_first_crossing
#print axioms result

end D5.S0.Computability.BinaryMachine.Machine3626
