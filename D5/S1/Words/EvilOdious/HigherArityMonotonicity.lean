/- GID: D5/S1/Words/EvilOdious/HigherArityMonotonicity
   generality: I
   mirror-B: D5/B/S1/Words/EvilOdious/HigherArityMonotonicity
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Finite-prefix convolution correction and higher-arity evil-odious monotonicity. -/

/-
admission_basis: escape-witness
Module escape_witness: evil_odious_pair_convolution_and_bound, quantified_finite_prefix_correction, higher_arity_evil_odious_strict_monotonicity
Escape witnesses surviving the bypass test:
1. evil_odious_pair_convolution_and_bound:
   Filtered Finset.Nat.antidiagonalTuple first-coordinate peeling bijection (Fin.cons/Fin.tail)
   establishing r (k + 1) n = natConv evilInd (r k) n and s (k + 1) n = natConv odiousInd (s k) n;
   coordinatewise +1 shift bijection establishing positiveEvilCount k (n + k) = r k n and
   positiveOdiousCount k (n + k) = s k n; and inductive weak-composition cardinality
   (Finset.Nat.antidiagonalTuple k n).card = Nat.choose (n + k - 1) (k - 1) yielding the binomial
   upper bounds on r k n and s k n for all k >= 1.
2. quantified_finite_prefix_correction:
   Signed difference-convolution decomposition into endpoint a(n + 1) f(0), reindexed finite
   prefix 0 <= m < R, and tail 0 <= j <= n - R; pair-complementation lower bound
   (n - R + 1) / 2 <= sum_{j=0}^{n-R} a(j); weighted and unweighted prefix-variation bounds
   yielding delta g(n) >= 1 for n >= R + 2 * prefixVar R f + 1; and cumulative hockey-stick
   identity sum_{m=0}^{R-1} choose(m + k - 1, k - 1) = choose(R + k - 1, k).
3. higher_arity_evil_odious_strict_monotonicity:
   Inductive propagation from SixfoldMonotonicity.result across all k >= 6, combining
   quantified_finite_prefix_correction with evil_odious_pair_convolution_and_bound on the evil
   branch above evilBound k, shifted-odious bijection s k n = shiftedOdious k (n - k) and global
   difference-convolution monotonicity on the odious branch for n >= k - 1 (hence n >= odiousBound
   k), and symbolic arity-7 thresholds evilBound 7 = 38 + 2 * Nat.choose 42 6, odiousBound 7 = 426.
Direct frozen dependencies: aliases below denote declaration identities, not module pins.
T0 = D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.thueMorse
  statement_id: sha256:64e3518f7565865a40ea42fed02d3ec99a43a5957584903476dff7ab488bd8b0
T1 = D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.thueMorse_zero
  statement_id: sha256:3fd066872112014dfb8ef3c50068b4e1725e86b23fca3bc32fd129543beddb1d
T2 = D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.thueMorse_two_mul
  statement_id: sha256:af72ea11dc2767d57ddea36081e67b10dac11b1446c37bc278152529b8495829
T3 = D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.thueMorse_two_mul_add_one
  statement_id: sha256:bd88293e547144a1fa04ae9e8252479189777a1fbc1a709252b2d8882d7697c4
T4 = D5/S1/Words/EvilOdious/SequenceCoefficients.r
  statement_id: sha256:43c3a20888da491b7491a4ab4442bf534f897ae3087443c6a35cb0855c39bf5b
T5 = D5/S1/Words/EvilOdious/SequenceCoefficients.s
  statement_id: sha256:9c99454ea2ca93c85e52783957979d94a0e73a8b4af942ac143489b097418a5a
T6 = D5/S1/Words/EvilOdious/SixfoldMonotonicity.result
  statement_id: sha256:f74b065d4ca3b2d647f18266954c75d66443aafbd417a27a93e2ef56b4d6279a
Utility: none; universally quantified discrete convolution bounds and higher-arity monotonicity.
Declaration rows: name | proof_shape | frozen dependencies | escape_witness | consumers.
Definitions carry not-applicable as an organization label; no proof content is claimed for them.
evilInd | proof_shape: not-applicable | frozen: T0 | escape_witness: none | consumers: HigherArityMonotonicity.evil_odious_pair_convolution_and_bound, HigherArityMonotonicity.higher_arity_evil_odious_strict_monotonicity
odiousInd | proof_shape: not-applicable | frozen: T0 | escape_witness: none | consumers: HigherArityMonotonicity.evil_odious_pair_convolution_and_bound
natConv | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: HigherArityMonotonicity.tupleCount_succ, HigherArityMonotonicity.antidiagonalTuple_card, HigherArityMonotonicity.evil_odious_pair_convolution_and_bound, HigherArityMonotonicity.fwdDiff_natConv, HigherArityMonotonicity.quantified_finite_prefix_correction, HigherArityMonotonicity.higher_arity_evil_odious_strict_monotonicity
shiftedOdious | proof_shape: not-applicable | frozen: T0 | escape_witness: none | consumers: HigherArityMonotonicity.higher_arity_evil_odious_strict_monotonicity
positiveEvilCount | proof_shape: not-applicable | frozen: T0 | escape_witness: none | consumers: HigherArityMonotonicity.evil_odious_pair_convolution_and_bound
positiveOdiousCount | proof_shape: not-applicable | frozen: T0 | escape_witness: none | consumers: HigherArityMonotonicity.evil_odious_pair_convolution_and_bound
fwdDiff | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: HigherArityMonotonicity.prefixVarInt, HigherArityMonotonicity.fwdDiff_natConv, HigherArityMonotonicity.quantified_finite_prefix_correction, HigherArityMonotonicity.higher_arity_evil_odious_strict_monotonicity
negPart | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: HigherArityMonotonicity.prefixVarInt, HigherArityMonotonicity.quantified_finite_prefix_correction
prefixVarInt | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: HigherArityMonotonicity.prefixVar, HigherArityMonotonicity.quantified_finite_prefix_correction
prefixVar | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: HigherArityMonotonicity.quantified_finite_prefix_correction
evilBound | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: HigherArityMonotonicity.higher_arity_evil_odious_strict_monotonicity
odiousBound | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: HigherArityMonotonicity.higher_arity_evil_odious_strict_monotonicity
tupleCount | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: HigherArityMonotonicity.tupleCount_zero, HigherArityMonotonicity.tupleCount_succ, HigherArityMonotonicity.antidiagonalTuple_card, HigherArityMonotonicity.evil_odious_pair_convolution_and_bound
tupleCount_zero | proof_shape: content | frozen: none | escape_witness: D5.S1.Words.EvilOdious.HigherArityMonotonicity.tupleCount_zero | consumers: HigherArityMonotonicity.antidiagonalTuple_card, HigherArityMonotonicity.evil_odious_pair_convolution_and_bound
tupleCount_succ | proof_shape: content | frozen: none | escape_witness: D5.S1.Words.EvilOdious.HigherArityMonotonicity.tupleCount_succ | consumers: HigherArityMonotonicity.antidiagonalTuple_card, HigherArityMonotonicity.evil_odious_pair_convolution_and_bound, HigherArityMonotonicity.higher_arity_evil_odious_strict_monotonicity
sum_choose_hockey_stick | proof_shape: content | frozen: none | escape_witness: D5.S1.Words.EvilOdious.HigherArityMonotonicity.sum_choose_hockey_stick | consumers: HigherArityMonotonicity.antidiagonalTuple_card, HigherArityMonotonicity.quantified_finite_prefix_correction
antidiagonalTuple_card | proof_shape: content | frozen: none | escape_witness: D5.S1.Words.EvilOdious.HigherArityMonotonicity.tupleCount_zero, D5.S1.Words.EvilOdious.HigherArityMonotonicity.tupleCount_succ, D5.S1.Words.EvilOdious.HigherArityMonotonicity.sum_choose_hockey_stick | consumers: HigherArityMonotonicity.evil_odious_pair_convolution_and_bound
positiveShift_card | proof_shape: content | frozen: none | escape_witness: D5.S1.Words.EvilOdious.HigherArityMonotonicity.positiveShift_card | consumers: HigherArityMonotonicity.evil_odious_pair_convolution_and_bound, HigherArityMonotonicity.higher_arity_evil_odious_strict_monotonicity
evil_odious_pair_convolution_and_bound | proof_shape: content | frozen: T0,T2,T3,T4,T5 | escape_witness: D5.S1.Words.EvilOdious.HigherArityMonotonicity.tupleCount_zero, D5.S1.Words.EvilOdious.HigherArityMonotonicity.tupleCount_succ, D5.S1.Words.EvilOdious.HigherArityMonotonicity.antidiagonalTuple_card, D5.S1.Words.EvilOdious.HigherArityMonotonicity.positiveShift_card | consumers: HigherArityMonotonicity.higher_arity_evil_odious_strict_monotonicity
fwdDiff_natConv | proof_shape: content | frozen: none | escape_witness: D5.S1.Words.EvilOdious.HigherArityMonotonicity.fwdDiff_natConv | consumers: HigherArityMonotonicity.quantified_finite_prefix_correction, HigherArityMonotonicity.higher_arity_evil_odious_strict_monotonicity
pair_complementation_binary_and_sum | proof_shape: content | frozen: none | escape_witness: D5.S1.Words.EvilOdious.HigherArityMonotonicity.pair_complementation_binary_and_sum | consumers: HigherArityMonotonicity.quantified_finite_prefix_correction
quantified_finite_prefix_correction | proof_shape: content | frozen: none | escape_witness: D5.S1.Words.EvilOdious.HigherArityMonotonicity.fwdDiff_natConv, D5.S1.Words.EvilOdious.HigherArityMonotonicity.pair_complementation_binary_and_sum, D5.S1.Words.EvilOdious.HigherArityMonotonicity.sum_choose_hockey_stick | consumers: HigherArityMonotonicity.higher_arity_evil_odious_strict_monotonicity
higher_arity_evil_odious_strict_monotonicity | proof_shape: content | frozen: T0,T1,T3,T4,T5,T6 | escape_witness: D5.S1.Words.EvilOdious.HigherArityMonotonicity.evil_odious_pair_convolution_and_bound, D5.S1.Words.EvilOdious.HigherArityMonotonicity.quantified_finite_prefix_correction, D5.S1.Words.EvilOdious.HigherArityMonotonicity.tupleCount_succ, D5.S1.Words.EvilOdious.HigherArityMonotonicity.positiveShift_card, D5.S1.Words.EvilOdious.HigherArityMonotonicity.fwdDiff_natConv | consumers: none
-/

import D5.S1.Words.Complexity.ThueMorseReducedAbelianOdd
import D5.S1.Words.EvilOdious.SequenceCoefficients
import D5.S1.Words.EvilOdious.SixfoldMonotonicity

/-! # Quantified Finite-Prefix Convolution Correction and Higher-Arity Evil-Odious Monotonicity -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

namespace D5.S1.Words.EvilOdious.HigherArityMonotonicity

open D5.S1.Words.Complexity
open D5.S1.Words.EvilOdious.SequenceCoefficients

/-- Indicator function of the evil support `{n : ℕ | thueMorse n = false}` in `{0, 1}`. -/
def evilInd (n : ℕ) : ℕ := if thueMorse n = false then 1 else 0
/-- Indicator function of the odious support `{n : ℕ | thueMorse n = true}` in `{0, 1}`. -/
def odiousInd (n : ℕ) : ℕ := if thueMorse n = true then 1 else 0
/-- Discrete convolution `(a * f)(n) = ∑_{j=0}^n a(j) f(n - j)` of two natural sequences. -/
def natConv (a f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), a j * f (n - j)
/-- Ordered `k`-tuple representation count of `m` over `{b : ℕ | thueMorse (b + 1) = true}`. -/
def shiftedOdious (k m : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple k m).filter (fun b => ∀ i, thueMorse (b i + 1) = true)).card
/-- Ordered `k`-tuple representation count of `N` over the shifted evil support `E + 1`. -/
def positiveEvilCount (k N : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple k N).filter
    (fun x => ∀ i, 1 ≤ x i ∧ thueMorse (x i - 1) = false)).card
/-- Ordered `k`-tuple representation count of `N` over the shifted odious support `O + 1`. -/
def positiveOdiousCount (k N : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple k N).filter
    (fun x => ∀ i, 1 ≤ x i ∧ thueMorse (x i - 1) = true)).card
/-- Signed integer forward difference `δf(m) = (f(m + 1) : ℤ) - (f(m) : ℤ)`. -/
def fwdDiff (f : ℕ → ℕ) (m : ℕ) : ℤ := (f (m + 1) : ℤ) - (f m : ℤ)
/-- Integer negative part `u_- = max(0, -u)`. -/
def negPart (u : ℤ) : ℤ := max (0 : ℤ) (-u)
/-- Integer-valued cumulative negative forward-difference variation on `[0, R)`. -/
def prefixVarInt (R : ℕ) (f : ℕ → ℕ) : ℤ := ∑ m ∈ Finset.range R, negPart (fwdDiff f m)
/-- Natural-valued cumulative negative forward-difference variation on `[0, R)`. -/
def prefixVar (R : ℕ) (f : ℕ → ℕ) : ℕ := (prefixVarInt R f).toNat
/-- Recursive sufficient threshold sequence `R_{r, k}` seeded by `R_{r, 6} = 37`. -/
def evilBound : ℕ → ℕ
  | 0 => 37
  | k + 1 => if k < 6 then 37 else evilBound k + 2 * Nat.choose (evilBound k + k - 1) k + 1
/-- Recursive sufficient threshold sequence `R_{s, k}` seeded by `R_{s, 6} = 5`. -/
def odiousBound : ℕ → ℕ
  | 0 => 5
  | k + 1 => if k < 6 then 5 else odiousBound k + 2 * Nat.choose (odiousBound k + k - 1) k + 1

private def tupleCount (P : ℕ → Bool) (k n : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple k n).filter (fun x => ∀ i, P (x i) = true)).card

private theorem tupleCount_zero (P : ℕ → Bool) (n : ℕ) :
    tupleCount P 0 n = if n = 0 then 1 else 0 := by
  unfold tupleCount; split_ifs with hn
  · subst hn
    have hset : (Finset.Nat.antidiagonalTuple 0 0).filter
        (fun x => ∀ i, P (x i) = true) = {Fin.elim0} := by
      ext x; simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, Finset.univ_eq_empty,
        Finset.sum_empty, true_and, Finset.mem_singleton]
      exact ⟨fun _ => funext (fun i => Fin.elim0 i), fun _ i => Fin.elim0 i⟩
    rw [hset, Finset.card_singleton]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro x hx _
    have h0 : (0 : ℕ) = n := by simpa [Finset.Nat.mem_antidiagonalTuple] using hx
    exact hn h0.symm

private theorem tupleCount_succ (P : ℕ → Bool) (k n : ℕ) :
    tupleCount P (k + 1) n =
      natConv (fun j => if P j = true then 1 else 0) (tupleCount P k) n := by
  unfold tupleCount natConv
  let S := (Finset.Nat.antidiagonalTuple (k + 1) n).filter (fun x => ∀ i, P (x i) = true)
  have hmaps : ∀ x ∈ S, x 0 ∈ Finset.range (n + 1) := by
    intro x hx; have hsum := Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp hx).1
    rw [Fin.sum_univ_succ] at hsum; exact Finset.mem_range.mpr (by omega)
  rw [show S.card = ∑ j ∈ Finset.range (n + 1), (S.filter (fun x => x 0 = j)).card from
    Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl; intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  cases hpj : P j with
  | true =>
      simp only [hpj, ↓reduceIte, one_mul]; symm
      refine Finset.card_bij (fun (y : Fin k → ℕ) _ => Fin.cons j y) ?_ ?_ ?_
      · intro y hy; rcases Finset.mem_filter.mp hy with ⟨hysum, hyP⟩
        have hysum' := Finset.Nat.mem_antidiagonalTuple.mp hysum
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
        · rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ, Fin.cons_zero]
          simp only [Fin.cons_succ]; omega
        · intro i; refine Fin.cases (by simpa only [Fin.cons_zero] using hpj)
            (fun i' => by simpa only [Fin.cons_succ] using hyP i') i
      · exact fun y₁ _ y₂ _ hcons => by simpa only [Fin.tail_cons] using congrArg Fin.tail hcons
      · intro x hx; rcases Finset.mem_filter.mp hx with ⟨hxS, hx0⟩
        rcases Finset.mem_filter.mp hxS with ⟨hxsum, hxP⟩
        have hxsum' := Finset.Nat.mem_antidiagonalTuple.mp hxsum
        rw [Fin.sum_univ_succ, hx0] at hxsum'
        refine ⟨Fin.tail x, Finset.mem_filter.mpr ⟨?_, fun i => hxP i.succ⟩,
          by rw [← hx0, Fin.cons_self_tail]⟩
        rw [Finset.Nat.mem_antidiagonalTuple]; change (∑ i : Fin k, x i.succ) = n - j; omega
  | false =>
      simp only [hpj, Bool.false_eq_true, ↓reduceIte, zero_mul]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro x hxS hx0
      have hxP := (Finset.mem_filter.mp hxS).2 0; rw [hx0, hpj] at hxP; cases hxP

private theorem sum_choose_hockey_stick (R k : ℕ) (hk : 1 ≤ k) :
    (∑ m ∈ Finset.range R, Nat.choose (m + k - 1) (k - 1)) = Nat.choose (R + k - 1) k := by
  induction R with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  | succ R ih =>
      rw [Finset.sum_range_succ, ih]; obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [show R + (j + 1) - 1 = R + j by omega, show R + 1 + (j + 1) - 1 = (R + j) + 1 by omega,
        show j + 1 - 1 = j by omega, Nat.add_comm, Nat.choose_succ_succ]

private theorem antidiagonalTuple_card (k n : ℕ) (hk : 1 ≤ k) :
    (Finset.Nat.antidiagonalTuple k n).card = Nat.choose (n + k - 1) (k - 1) := by
  have hall : ∀ d m : ℕ,
      tupleCount (fun _ => true) (d + 1) m = Nat.choose (m + (d + 1) - 1) d := by
    intro d; induction d with
    | zero =>
        intro m; rw [tupleCount_succ]; unfold natConv; rw [Finset.sum_eq_single m]
        · simp [tupleCount_zero]
        · intro j hj _
          have hjn : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          simp [tupleCount_zero, show m - j ≠ 0 by omega]
        · exact fun hm => (hm (Finset.mem_range.mpr (Nat.lt_succ_self m))).elim
    | succ d ih =>
        intro m; rw [tupleCount_succ]; unfold natConv
        have hrev :
            (∑ j ∈ Finset.range (m + 1),
                (if true = true then 1 else 0) * tupleCount (fun _ => true) (d + 1) (m - j)) =
              ∑ j ∈ Finset.range (m + 1), tupleCount (fun _ => true) (d + 1) j := by
          simp only [↓reduceIte, one_mul]
          simpa only [Nat.add_sub_cancel] using
            (Finset.sum_range_reflect (fun x => tupleCount (fun _ => true) (d + 1) x) (m + 1))
        rw [hrev, show (∑ j ∈ Finset.range (m + 1), tupleCount (fun _ => true) (d + 1) j) =
            ∑ j ∈ Finset.range (m + 1), Nat.choose (j + (d + 1) - 1) ((d + 1) - 1) from
          Finset.sum_congr rfl (fun j _ => by simpa using ih j),
          sum_choose_hockey_stick (m + 1) (d + 1) (by omega)]
        congr 1; omega
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  have htrue : (Finset.Nat.antidiagonalTuple (d + 1) n).card =
      tupleCount (fun _ => true) (d + 1) n := by unfold tupleCount; simp
  rw [htrue, hall d n]; simp

private theorem positiveShift_card (Q : ℕ → Prop) [DecidablePred Q] (k n : ℕ) :
    ((Finset.Nat.antidiagonalTuple k (n + k)).filter
      (fun x => ∀ i, 1 ≤ x i ∧ Q (x i - 1))).card =
    ((Finset.Nat.antidiagonalTuple k n).filter (fun a => ∀ i, Q (a i))).card := by
  symm; refine Finset.card_bij (fun (a : Fin k → ℕ) _ i => a i + 1) ?_ ?_ ?_
  · intro a ha; rcases Finset.mem_filter.mp ha with ⟨hasum, haQ⟩
    have hasum' := Finset.Nat.mem_antidiagonalTuple.mp hasum
    refine Finset.mem_filter.mpr ⟨?_, fun i => ⟨Nat.le_add_left 1 (a i), by simpa using haQ i⟩⟩
    rw [Finset.Nat.mem_antidiagonalTuple, Finset.sum_add_distrib, hasum']; simp
  · exact fun a₁ _ a₂ _ h => funext (fun i => Nat.add_right_cancel (congrFun h i))
  · intro x hx; rcases Finset.mem_filter.mp hx with ⟨hxsum, hxQ⟩
    have hxsum' := Finset.Nat.mem_antidiagonalTuple.mp hxsum
    refine ⟨fun i => x i - 1, Finset.mem_filter.mpr ⟨?_, fun i => (hxQ i).2⟩,
      funext (fun i => Nat.sub_add_cancel (hxQ i).1)⟩
    rw [Finset.Nat.mem_antidiagonalTuple]
    have hpoint : ∑ i : Fin k, ((x i - 1) + 1) = ∑ i : Fin k, x i :=
      Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (hxQ i).1)
    rw [Finset.sum_add_distrib] at hpoint
    have hrestore : (∑ i : Fin k, (x i - 1)) + k = ∑ i : Fin k, x i := by simpa using hpoint
    omega

/-- Indicator binary-valuedness, adjacent-pair complementation, arity-1 agreement, ordered-tuple
convolution recurrences, weak-composition binomial upper bounds, and positive-coordinate shift
correspondences for the evil and odious representation counts `r` and `s`. -/
theorem evil_odious_pair_convolution_and_bound :
    (∀ q : ℕ, evilInd (2 * q) + evilInd (2 * q + 1) = 1) ∧
    (∀ q : ℕ, odiousInd (2 * q) + odiousInd (2 * q + 1) = 1) ∧
    (∀ n : ℕ, (evilInd n = 0 ∨ evilInd n = 1) ∧ (odiousInd n = 0 ∨ odiousInd n = 1) ∧
      r 1 n = evilInd n ∧ s 1 n = odiousInd n) ∧
    (∀ k n : ℕ, r (k + 1) n = natConv evilInd (r k) n ∧
      s (k + 1) n = natConv odiousInd (s k) n) ∧
    (∀ k n : ℕ, 1 ≤ k →
      r k n ≤ Nat.choose (n + k - 1) (k - 1) ∧
      s k n ≤ Nat.choose (n + k - 1) (k - 1)) ∧
    (∀ k n : ℕ, positiveEvilCount k (n + k) = r k n ∧
      positiveOdiousCount k (n + k) = s k n) := by
  have hr_tc : ∀ k n : ℕ, r k n = tupleCount (fun m => !thueMorse m) k n := by
    intro k n; unfold r tupleCount; congr 1; apply Finset.filter_congr; intro x _
    constructor <;> intro h i <;> specialize h i <;> cases htm : thueMorse (x i) <;> simp_all
  have hevil_ind : (fun j => if (!thueMorse j) = true then 1 else 0) = evilInd := by
    funext j; unfold evilInd; cases thueMorse j <;> rfl
  have hconv_r : ∀ k n : ℕ, r (k + 1) n = natConv evilInd (r k) n := by
    intro k n; rw [hr_tc (k + 1) n, tupleCount_succ, hevil_ind]
    exact Finset.sum_congr rfl (fun j _ => by rw [hr_tc])
  have hconv_s : ∀ k n : ℕ, s (k + 1) n = natConv odiousInd (s k) n :=
    fun k n => tupleCount_succ thueMorse k n
  refine ⟨?_, ?_, ?_, fun k n => ⟨hconv_r k n, hconv_s k n⟩, ?_, ?_⟩
  · intro q; unfold evilInd; rw [thueMorse_two_mul, thueMorse_two_mul_add_one]
    cases thueMorse q <;> rfl
  · intro q; unfold odiousInd; rw [thueMorse_two_mul, thueMorse_two_mul_add_one]
    cases thueMorse q <;> rfl
  · intro n
    refine ⟨by unfold evilInd; cases thueMorse n <;> simp,
      by unfold odiousInd; cases thueMorse n <;> simp, ?_, ?_⟩
    · rw [hconv_r 0 n]; unfold natConv; rw [Finset.sum_eq_single n]
      · simp [hr_tc, tupleCount_zero]
      · intro j hj _; have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hsub : n - j ≠ 0 := by omega
        simp only [hr_tc, tupleCount_zero, hsub, ↓reduceIte, mul_zero]
      · exact fun hn => (hn (Finset.mem_range.mpr (Nat.lt_succ_self n))).elim
    · rw [hconv_s 0 n]; unfold natConv; rw [Finset.sum_eq_single n]
      · change odiousInd n * tupleCount thueMorse 0 (n - n) = odiousInd n; simp [tupleCount_zero]
      · intro j hj _; have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hsub : n - j ≠ 0 := by omega
        change odiousInd j * tupleCount thueMorse 0 (n - j) = 0
        simp only [tupleCount_zero, hsub, ↓reduceIte, mul_zero]
      · exact fun hn => (hn (Finset.mem_range.mpr (Nat.lt_succ_self n))).elim
  · intro k n hk; rw [← antidiagonalTuple_card k n hk]
    exact ⟨Finset.card_filter_le _ _, Finset.card_filter_le _ _⟩
  · exact fun k n => ⟨positiveShift_card (fun m => thueMorse m = false) k n,
      positiveShift_card (fun m => thueMorse m = true) k n⟩

private theorem fwdDiff_natConv (a f : ℕ → ℕ) (n : ℕ) :
    fwdDiff (natConv a f) n =
      (a (n + 1) : ℤ) * (f 0 : ℤ) +
        ∑ j ∈ Finset.range (n + 1), (a j : ℤ) * fwdDiff f (n - j) := by
  unfold fwdDiff natConv; rw [Finset.sum_range_succ, Nat.sub_self]; push_cast
  have hshift :
      (∑ x ∈ Finset.range (n + 1), (a x : ℤ) * (f (n + 1 - x) : ℤ)) =
        ∑ x ∈ Finset.range (n + 1), (a x : ℤ) * (f (n - x + 1) : ℤ) :=
    Finset.sum_congr rfl (fun j hj => by
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [show n + 1 - j = n - j + 1 by omega])
  rw [hshift]
  have hdiff :
      (∑ j ∈ Finset.range (n + 1), (a j : ℤ) * (f (n - j + 1) : ℤ)) -
          (∑ j ∈ Finset.range (n + 1), (a j : ℤ) * (f (n - j) : ℤ)) =
        ∑ j ∈ Finset.range (n + 1),
          (a j : ℤ) * ((f (n - j + 1) : ℤ) - (f (n - j) : ℤ)) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
  linarith

private theorem pair_complementation_binary_and_sum
    (a : ℕ → ℕ) (ha : ∀ q : ℕ, a (2 * q) + a (2 * q + 1) = 1) :
    (∀ m : ℕ, a m = 0 ∨ a m = 1) ∧ (∀ L : ℕ, L / 2 ≤ ∑ j ∈ Finset.range L, a j) := by
  have hbin : ∀ m : ℕ, a m = 0 ∨ a m = 1 := by
    intro m; have hq := ha (m / 2)
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm
    · rw [show 2 * (m / 2) = m by omega] at hq; omega
    · rw [show 2 * (m / 2) + 1 = m by omega] at hq; omega
  have heven : ∀ k : ℕ, (∑ j ∈ Finset.range (2 * k), a j) = k := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Finset.sum_range_succ,
          Finset.sum_range_succ, ih, add_assoc, ha k]
  refine ⟨hbin, fun L => ?_⟩
  calc L / 2 = ∑ j ∈ Finset.range (2 * (L / 2)), a j := (heven (L / 2)).symm
    _ ≤ ∑ j ∈ Finset.range L, a j :=
      Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.mul_div_le L 2))

/-- Quantified finite-prefix convolution correction: under adjacent-pair complementation
`a(2q) + a(2q + 1) = 1` and tail forward-difference positivity `δf(m) ≥ 1` for `m ≥ R`, the
convolution `g = natConv a f` satisfies binary-valuedness of `a`, exact `ℕ`/`ℤ` variation
agreement, the three-tier difference identity and prefix-variation bounds on `n ≥ R`, the
general threshold `δg(n) ≥ 1` for `n ≥ R + 2 V_R(f) + 1`, the cumulative binomial hockey-stick
identity, and the binomial-bounded specialization `V_R(f) ≤ choose(R + k - 1, k)` with
`δg(n) ≥ 1` for `n ≥ R + 2 choose(R + k - 1, k) + 1`. -/
theorem quantified_finite_prefix_correction
    (a f : ℕ → ℕ) (R : ℕ)
    (ha : ∀ q : ℕ, a (2 * q) + a (2 * q + 1) = 1)
    (hf : ∀ m : ℕ, R ≤ m → (1 : ℤ) ≤ fwdDiff f m) :
    (∀ m : ℕ, a m = 0 ∨ a m = 1) ∧
    ((prefixVar R f : ℤ) = prefixVarInt R f) ∧
    (∀ n : ℕ, R ≤ n →
      fwdDiff (natConv a f) n =
        (a (n + 1) : ℤ) * (f 0 : ℤ) +
          (∑ m ∈ Finset.range R, (a (n - m) : ℤ) * fwdDiff f m) +
          (∑ j ∈ Finset.range (n - R + 1), (a j : ℤ) * fwdDiff f (n - j)) ∧
      (a (n + 1) : ℤ) * (f 0 : ℤ) + (((n - R + 1) / 2 : ℕ) : ℤ) -
          (∑ m ∈ Finset.range R, (a (n - m) : ℤ) * negPart (fwdDiff f m)) ≤
        fwdDiff (natConv a f) n ∧
      (a (n + 1) : ℤ) * (f 0 : ℤ) + (((n - R + 1) / 2 : ℕ) : ℤ) - prefixVarInt R f ≤
        (a (n + 1) : ℤ) * (f 0 : ℤ) + (((n - R + 1) / 2 : ℕ) : ℤ) -
          (∑ m ∈ Finset.range R, (a (n - m) : ℤ) * negPart (fwdDiff f m)) ∧
      (a (n + 1) : ℤ) * (f 0 : ℤ) + (((n - R + 1) / 2 : ℕ) : ℤ) - prefixVarInt R f ≤
        fwdDiff (natConv a f) n) ∧
    (∀ n : ℕ, R + 2 * prefixVar R f + 1 ≤ n → (1 : ℤ) ≤ fwdDiff (natConv a f) n) ∧
    (∀ k : ℕ, 1 ≤ k →
      (∑ m ∈ Finset.range R, Nat.choose (m + k - 1) (k - 1)) = Nat.choose (R + k - 1) k) ∧
    (∀ k : ℕ, 1 ≤ k → (∀ m : ℕ, f m ≤ Nat.choose (m + k - 1) (k - 1)) →
      prefixVar R f ≤ Nat.choose (R + k - 1) k ∧
      (∀ n : ℕ, R + 2 * Nat.choose (R + k - 1) k + 1 ≤ n →
        (1 : ℤ) ≤ fwdDiff (natConv a f) n)) := by
  rcases pair_complementation_binary_and_sum a ha with ⟨hbin, hpairSum⟩
  have ha_le_one : ∀ m : ℕ, (a m : ℤ) ≤ 1 := fun m => by
    rcases hbin m with hm | hm <;> simp [hm]
  have ha_nonneg : ∀ m : ℕ, (0 : ℤ) ≤ (a m : ℤ) := fun m => Nat.cast_nonneg (a m)
  have hcast : (prefixVar R f : ℤ) = prefixVarInt R f := by
    unfold prefixVar prefixVarInt negPart
    exact Int.toNat_of_nonneg (Finset.sum_nonneg (fun _ _ => le_max_left (0 : ℤ) _))
  have htiers (n : ℕ) (hn : R ≤ n) := by
    have hdecomp :
        fwdDiff (natConv a f) n =
          (a (n + 1) : ℤ) * (f 0 : ℤ) +
            (∑ m ∈ Finset.range R, (a (n - m) : ℤ) * fwdDiff f m) +
            (∑ j ∈ Finset.range (n - R + 1), (a j : ℤ) * fwdDiff f (n - j)) := by
      rw [fwdDiff_natConv, show n + 1 = (n - R + 1) + R by omega, Finset.sum_range_add]
      have hrefl :
          (∑ i ∈ Finset.range R, (a (n - R + 1 + i) : ℤ) * fwdDiff f (n - (n - R + 1 + i))) =
            ∑ m ∈ Finset.range R, (a (n - m) : ℤ) * fwdDiff f m := by
        rw [← Finset.sum_range_reflect (fun m => (a (n - m) : ℤ) * fwdDiff f m) R]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hiR : i < R := Finset.mem_range.mp hi
        have h1 : n - R + 1 + i = n - (R - 1 - i) := by omega
        have h2 : n - (n - R + 1 + i) = R - 1 - i := by omega
        rw [h2, h1]
      rw [hrefl]; ring
    have htail : (((n - R + 1) / 2 : ℕ) : ℤ) ≤
        ∑ j ∈ Finset.range (n - R + 1), (a j : ℤ) * fwdDiff f (n - j) := by
      have h1 : (((n - R + 1) / 2 : ℕ) : ℤ) ≤
          ((∑ j ∈ Finset.range (n - R + 1), a j : ℕ) : ℤ) :=
        Nat.cast_le.mpr (hpairSum (n - R + 1))
      rw [Nat.cast_sum] at h1
      refine le_trans h1 (Finset.sum_le_sum (fun j hj => ?_))
      have hjle : j ≤ n - R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf (n - j) (by omega)) (ha_nonneg j)
    have hpref : -(∑ m ∈ Finset.range R, (a (n - m) : ℤ) * negPart (fwdDiff f m)) ≤
        ∑ m ∈ Finset.range R, (a (n - m) : ℤ) * fwdDiff f m := by
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_le_sum (fun m _ => ?_)
      have hneg : -negPart (fwdDiff f m) ≤ fwdDiff f m := by
        unfold negPart; have hle := le_max_right (0 : ℤ) (-(fwdDiff f m)); linarith
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left hneg (ha_nonneg (n - m))
    have hvar : (∑ m ∈ Finset.range R, (a (n - m) : ℤ) * negPart (fwdDiff f m)) ≤
        prefixVarInt R f := by
      unfold prefixVarInt negPart; exact Finset.sum_le_sum (fun m _ => by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (ha_le_one (n - m)) (le_max_left (0 : ℤ) _))
    have h2 : (a (n + 1) : ℤ) * (f 0 : ℤ) + (((n - R + 1) / 2 : ℕ) : ℤ) -
        (∑ m ∈ Finset.range R, (a (n - m) : ℤ) * negPart (fwdDiff f m)) ≤
      fwdDiff (natConv a f) n := by linarith
    have h23 : (a (n + 1) : ℤ) * (f 0 : ℤ) + (((n - R + 1) / 2 : ℕ) : ℤ) - prefixVarInt R f ≤
        (a (n + 1) : ℤ) * (f 0 : ℤ) + (((n - R + 1) / 2 : ℕ) : ℤ) -
          (∑ m ∈ Finset.range R, (a (n - m) : ℤ) * negPart (fwdDiff f m)) := by linarith
    exact And.intro hdecomp (And.intro h2 (And.intro h23 (le_trans h23 h2)))
  have hthresh : ∀ n : ℕ, R + 2 * prefixVar R f + 1 ≤ n →
      (1 : ℤ) ≤ fwdDiff (natConv a f) n := by
    intro n hn; have htier3 := (htiers n (by omega)).2.2.2
    have hdivZ : (prefixVar R f : ℤ) + 1 ≤ (((n - R + 1) / 2 : ℕ) : ℤ) := by
      exact_mod_cast (show prefixVar R f + 1 ≤ (n - R + 1) / 2 by omega)
    have hnonneg := mul_nonneg (ha_nonneg (n + 1)) (Nat.cast_nonneg (f 0))
    linarith
  refine ⟨hbin, hcast, htiers, hthresh, fun k hk => sum_choose_hockey_stick R k hk, ?_⟩
  intro k hk hfbnd
  have hvar_bnd : prefixVar R f ≤ Nat.choose (R + k - 1) k := by
    have hvarZ : prefixVarInt R f ≤ (Nat.choose (R + k - 1) k : ℤ) := by
      rw [← sum_choose_hockey_stick R k hk, Nat.cast_sum]
      refine Finset.sum_le_sum (fun m _ => ?_)
      have hneg_le : negPart (fwdDiff f m) ≤ (f m : ℤ) := by
        unfold negPart fwdDiff; refine max_le (Nat.cast_nonneg (f m)) ?_
        have hfm1 : (0 : ℤ) ≤ (f (m + 1) : ℤ) := Nat.cast_nonneg (f (m + 1)); linarith
      exact le_trans hneg_le (Nat.cast_le.mpr (hfbnd m))
    rw [← hcast] at hvarZ; exact Nat.cast_le.mp hvarZ
  exact ⟨hvar_bnd, fun n hn => hthresh n (by omega)⟩

/-- Higher-arity strict monotonicity for evil and odious ordered representation counts: exact
base and recursive threshold equations for `evilBound` and `odiousBound` across all `k ≥ 6`,
exact arity-7 values `evilBound 7 = 38 + 2 * Nat.choose 42 6` and `odiousBound 7 = 426`, the
shifted-odious bijection `s k n = shiftedOdious k (n - k)` for `k ≥ 1`, global strict increase
of `shiftedOdious k` and sharp odious strict increase `s k n < s k (n + 1)` on `n ≥ k - 1` for
all `k ≥ 6`, and quantitative strict increase `r k n < r k (n + 1)` for `n ≥ evilBound k` and
`s k n < s k (n + 1)` for `n ≥ odiousBound k` across all `k ≥ 6`. -/
theorem higher_arity_evil_odious_strict_monotonicity :
    evilBound 6 = 37 ∧
    odiousBound 6 = 5 ∧
    (∀ k : ℕ, 6 ≤ k →
      evilBound (k + 1) = evilBound k + 2 * Nat.choose (evilBound k + k - 1) k + 1 ∧
      odiousBound (k + 1) = odiousBound k + 2 * Nat.choose (odiousBound k + k - 1) k + 1) ∧
    evilBound 7 = 38 + 2 * Nat.choose 42 6 ∧
    odiousBound 7 = 426 ∧
    (∀ k : ℕ, 1 ≤ k →
      shiftedOdious k 0 = 1 ∧
      (∀ n : ℕ, n < k → s k n = 0) ∧
      (∀ n : ℕ, k ≤ n → s k n = shiftedOdious k (n - k))) ∧
    (∀ k : ℕ, 6 ≤ k → ∀ m : ℕ, shiftedOdious k m < shiftedOdious k (m + 1)) ∧
    (∀ k : ℕ, 6 ≤ k → ∀ n : ℕ, k - 1 ≤ n → s k n < s k (n + 1)) ∧
    (∀ k : ℕ, 6 ≤ k → ∀ n : ℕ, evilBound k ≤ n → r k n < r k (n + 1)) ∧
    (∀ k : ℕ, 6 ≤ k → ∀ n : ℕ, odiousBound k ≤ n → s k n < s k (n + 1)) := by
  have he6 : evilBound 6 = 37 := rfl
  have ho6 : odiousBound 6 = 5 := rfl
  have he_rec (k : ℕ) (hk : 6 ≤ k) :
      evilBound (k + 1) = evilBound k + 2 * Nat.choose (evilBound k + k - 1) k + 1 := by
    simp [evilBound, show ¬ k < 6 by omega]
  have ho_rec (k : ℕ) (hk : 6 ≤ k) :
      odiousBound (k + 1) = odiousBound k + 2 * Nat.choose (odiousBound k + k - 1) k + 1 := by
    simp [odiousBound, show ¬ k < 6 by omega]
  have hsix_r : ∀ n ≥ 37, r 6 n < r 6 (n + 1) := SixfoldMonotonicity.result.2.1
  have hsix_s : ∀ n ≥ 5, s 6 n < s 6 (n + 1) := SixfoldMonotonicity.result.2.2
  have hpair := evil_odious_pair_convolution_and_bound
  have he7 : evilBound 7 = 38 + 2 * Nat.choose 42 6 := by
    change evilBound (6 + 1) = 38 + 2 * Nat.choose 42 6; rw [he_rec 6 le_rfl, he6]
    change 37 + 2 * Nat.choose 42 6 + 1 = 38 + 2 * Nat.choose 42 6; omega
  have ho7 : odiousBound 7 = 426 := by decide
  have htm1 : thueMorse 1 = true := by simpa using thueMorse_two_mul_add_one 0
  have hshift_bij : ∀ k : ℕ, 1 ≤ k →
      shiftedOdious k 0 = 1 ∧
      (∀ n : ℕ, n < k → s k n = 0) ∧
      (∀ n : ℕ, k ≤ n → s k n = shiftedOdious k (n - k)) := by
    intro k _hk
    have hq0 : shiftedOdious k 0 = 1 := by
      unfold shiftedOdious
      have hset : (Finset.Nat.antidiagonalTuple k 0).filter
          (fun b => ∀ i, thueMorse (b i + 1) = true) = {fun _ => 0} := by
        ext b
        simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, Finset.mem_singleton]
        refine ⟨fun ⟨hsum, _⟩ => funext (fun i =>
          Finset.sum_eq_zero_iff.mp hsum i (Finset.mem_univ i)), ?_⟩
        rintro rfl; exact ⟨by simp, fun _ => by simpa using htm1⟩
      rw [hset, Finset.card_singleton]
    have hslt : ∀ n : ℕ, n < k → s k n = 0 := by
      intro n hnk; unfold s; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hxsum hx; have hsum := Finset.Nat.mem_antidiagonalTuple.mp hxsum
      have hpos : ∀ i : Fin k, 1 ≤ x i := fun i => by
        rcases Nat.eq_zero_or_pos (x i) with h0 | hp
        · have hf : thueMorse (x i) = false := by rw [h0, thueMorse_zero]
          rw [hx i] at hf; cases hf
        · exact hp
      have hge : k ≤ ∑ i : Fin k, x i := by
        calc k = ∑ _i : Fin k, 1 := by simp
          _ ≤ ∑ i : Fin k, x i := Finset.sum_le_sum (fun i _ => hpos i)
      omega
    have hsge : ∀ n : ℕ, k ≤ n → s k n = shiftedOdious k (n - k) := by
      intro n hkn
      have hfilt :
          (Finset.Nat.antidiagonalTuple k n).filter (fun x => ∀ i, thueMorse (x i) = true) =
            (Finset.Nat.antidiagonalTuple k ((n - k) + k)).filter
              (fun x => ∀ i, 1 ≤ x i ∧ thueMorse ((x i - 1) + 1) = true) := by
        rw [Nat.sub_add_cancel hkn]; apply Finset.filter_congr; intro x _; constructor
        · intro hx i
          have hpos : 1 ≤ x i := by
            rcases Nat.eq_zero_or_pos (x i) with h0 | hp
            · have hf : thueMorse (x i) = false := by rw [h0, thueMorse_zero]
              rw [hx i] at hf; cases hf
            · exact hp
          exact ⟨hpos, by rw [Nat.sub_add_cancel hpos]; exact hx i⟩
        · intro hx i; have h1 := (hx i).2; rw [Nat.sub_add_cancel (hx i).1] at h1; exact h1
      unfold s shiftedOdious; rw [hfilt]
      exact positiveShift_card (fun b => thueMorse (b + 1) = true) k (n - k)
    exact ⟨hq0, hslt, hsge⟩
  have hq_strict : ∀ k : ℕ, 6 ≤ k →
      ∀ m : ℕ, shiftedOdious k m < shiftedOdious k (m + 1) := by
    intro k hk; induction k, hk using Nat.le_induction with
    | base =>
        intro m; have hb6 := (hshift_bij 6 (by decide)).2.2
        have h1 : s 6 (m + 6) = shiftedOdious 6 m := by
          simpa only [Nat.add_sub_cancel] using hb6 (m + 6) (Nat.le_add_left 6 m)
        have h2 : s 6 (m + 6 + 1) = shiftedOdious 6 (m + 1) := by
          simpa only [show m + 6 + 1 - 6 = m + 1 by omega] using hb6 (m + 6 + 1) (by omega)
        rw [← h1, ← h2]; exact hsix_s (m + 6) (by omega)
    | succ k hk ih =>
        intro m
        let bInd : ℕ → ℕ := fun j => if thueMorse (j + 1) = true then 1 else 0
        have hq_conv : shiftedOdious (k + 1) = natConv bInd (shiftedOdious k) :=
          funext (fun u => tupleCount_succ (fun b => thueMorse (b + 1)) k u)
        have hdiff := fwdDiff_natConv bInd (shiftedOdious k) m; rw [← hq_conv] at hdiff
        have hterm_nonneg : ∀ j ∈ Finset.range (m + 1),
            (0 : ℤ) ≤ (bInd j : ℤ) * fwdDiff (shiftedOdious k) (m - j) := by
          intro j _; have hlt := ih (m - j)
          have hfd : (1 : ℤ) ≤ fwdDiff (shiftedOdious k) (m - j) := by unfold fwdDiff; omega
          exact mul_nonneg (Nat.cast_nonneg (bInd j)) (by linarith)
        have hsum_ge :=
          Finset.single_le_sum hterm_nonneg (Finset.mem_range.mpr (Nat.zero_lt_succ m))
        have hb0 : bInd 0 = 1 := by simp [bInd, htm1]
        have hltm := ih m
        have hfdm : (1 : ℤ) ≤ fwdDiff (shiftedOdious k) m := by unfold fwdDiff; omega
        have hend_nn : (0 : ℤ) ≤ (bInd (m + 1) : ℤ) * (shiftedOdious k 0 : ℤ) :=
          mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        rw [hb0, Nat.sub_zero] at hsum_ge; simp only [Nat.cast_one, one_mul] at hsum_ge
        have hfd_succ : (1 : ℤ) ≤ fwdDiff (shiftedOdious (k + 1)) m := by linarith
        unfold fwdDiff at hfd_succ; omega
  have hs_sharp : ∀ k : ℕ, 6 ≤ k → ∀ n : ℕ, k - 1 ≤ n → s k n < s k (n + 1) := by
    intro k hk n hn; obtain ⟨hq0, hslt, hsge⟩ := hshift_bij k (by omega)
    by_cases hnk : n < k
    · rw [hslt n hnk, show n + 1 = k by omega, hsge k le_rfl, Nat.sub_self, hq0]
      exact Nat.zero_lt_one
    · rw [hsge n (by omega), hsge (n + 1) (by omega), show n + 1 - k = n - k + 1 by omega]
      exact hq_strict k hk (n - k)
  have hr_mono : ∀ k : ℕ, 6 ≤ k →
      ∀ n : ℕ, evilBound k ≤ n → r k n < r k (n + 1) := by
    intro k hk; induction k, hk using Nat.le_induction with
    | base => intro n hn; rw [he6] at hn; exact hsix_r n hn
    | succ k hk ih =>
        intro n hn
        have hf_tail : ∀ m : ℕ, evilBound k ≤ m → (1 : ℤ) ≤ fwdDiff (r k) m := by
          intro m hm; have hlt := ih m hm; unfold fwdDiff; omega
        have hcorr := (quantified_finite_prefix_correction
            evilInd (r k) (evilBound k) hpair.1 hf_tail).2.2.2.2.2
          k (by omega) (fun m => (hpair.2.2.2.2.1 k m (by omega)).1)
        rw [he_rec k hk] at hn; have hfd := hcorr.2 n hn
        have hr_conv : natConv evilInd (r k) = r (k + 1) :=
          funext (fun u => (hpair.2.2.2.1 k u).1.symm)
        rw [hr_conv] at hfd; unfold fwdDiff at hfd; omega
  have hod_ge : ∀ k : ℕ, 6 ≤ k → k - 1 ≤ odiousBound k := by
    intro k hk; induction k, hk using Nat.le_induction with
    | base => decide
    | succ k hk ih => rw [ho_rec k hk]; omega
  have hs_mono : ∀ k : ℕ, 6 ≤ k →
      ∀ n : ℕ, odiousBound k ≤ n → s k n < s k (n + 1) :=
    fun k hk n hn => hs_sharp k hk n (le_trans (hod_ge k hk) hn)
  exact ⟨he6, ho6, fun k hk => ⟨he_rec k hk, ho_rec k hk⟩, he7, ho7,
    hshift_bij, hq_strict, hs_sharp, hr_mono, hs_mono⟩

end D5.S1.Words.EvilOdious.HigherArityMonotonicity
