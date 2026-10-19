/- GID: D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves Lee--Liu Conjecture 2.5: gamma2 (G_3,n) = floor (3n/2) + 1 for n >= 1. -/

/-
admission_basis: open-problem-resolution (#17651; Proved)
escape_witness: none
Direct frozen dependencies: F = D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.instDecidableRelFinAdjPathGraph_d5 (declaration statement_id sha256:337ad150a1d9869c2b2aaa2ac02c4f7553b8d5dfacb80d6baf8dbdaf6ece292c);
S = D5/S1/Digit/MaxDigitSumBase.digitSum (declaration statement_id sha256:685be4a14b25d5106de2047a418119ee94c199c83c1479e7d9ab2c7f142ce490).
In the declaration inventory below, frozen=F denotes the path-graph dependency; frozen=S denotes the digit-sum dependency, reused by the consumers of s.
Certificate slices use kernel decisions. The other proofs reduce the column encoding and the
Cartesian-product neighbour sets, sum the potential inequalities using Mathlib's telescoping
identity, count the alternating construction, and apply the natural-number infimum lemmas.
All declarations are classified bind-only; each helper has the listed mathematical consumers.
The claim retains the preregistered general-m definitions; proofs reuse the imported path-graph
decidability instance instead of declaring a second one. The base-three encoder uses finProdFinEquiv; zero padding uses Function.extend.
The public column_reduction theorem identifies grid domination with the zero-padded column inequalities for every row count.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17855.

s: proof_shape: bind-only; escape_witness: none; frozen=S; consumers: L1, L2, L2_00, L2_01, L2_02, L2_03, L2_04, L2_05, L2_06, L2_07, L2_08, L2_09, L2_10, L2_11, L2_12, L2_13, L2_14, L2_15, L2_16, L2_17, L2_18, L2_19, L2_20, L2_21, L2_22, L2_23, L2_24, L2_25, L2_26, Phi, digit_sum, lower_bound, potential_prefix, s_uc_formula, sequence_lower_bound, sum_uc, upper_weight, weight_columns.
A: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2, L2_00, L2_01, L2_02, L2_03, L2_04, L2_05, L2_06, L2_07, L2_08, L2_09, L2_10, L2_11, L2_12, L2_13, L2_14, L2_15, L2_16, L2_17, L2_18, L2_19, L2_20, L2_21, L2_22, L2_23, L2_24, L2_25, L2_26, L3, L3_00, L3_01, L3_02, L3_03, L3_04, L3_05, L3_06, L3_07, L3_08, L3_09, L3_10, L3_11, L3_12, L3_13, L3_14, L3_15, L3_16, L3_17, L3_18, L3_19, L3_20, L3_21, L3_22, L3_23, L3_24, L3_25, L3_26, aDecidable, cols_feasible, columnA_digit, potential_prefix, sequence_lower_bound, three_column_reduction, uc_feasible, upper_dominating.
aDecidable: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2_00, L2_01, L2_02, L2_03, L2_04, L2_05, L2_06, L2_07, L2_08, L2_09, L2_10, L2_11, L2_12, L2_13, L2_14, L2_15, L2_16, L2_17, L2_18, L2_19, L2_20, L2_21, L2_22, L2_23, L2_24, L2_25, L2_26, L3_00, L3_01, L3_02, L3_03, L3_04, L3_05, L3_06, L3_07, L3_08, L3_09, L3_10, L3_11, L3_12, L3_13, L3_14, L3_15, L3_16, L3_17, L3_18, L3_19, L3_20, L3_21, L3_22, L3_23, L3_24, L3_25, L3_26, uc_feasible.
R: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: Phi.
Phi: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L1, L2, L2_00, L2_01, L2_02, L2_03, L2_04, L2_05, L2_06, L2_07, L2_08, L2_09, L2_10, L2_11, L2_12, L2_13, L2_14, L2_15, L2_16, L2_17, L2_18, L2_19, L2_20, L2_21, L2_22, L2_23, L2_24, L2_25, L2_26, L3, L3_00, L3_01, L3_02, L3_03, L3_04, L3_05, L3_06, L3_07, L3_08, L3_09, L3_10, L3_11, L3_12, L3_13, L3_14, L3_15, L3_16, L3_17, L3_18, L3_19, L3_20, L3_21, L3_22, L3_23, L3_24, L3_25, L3_26, potential_prefix, sequence_lower_bound.
L1: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: potential_prefix.
L2_00: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_00: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_01: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_01: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_02: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_02: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_03: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_03: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_04: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_04: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_05: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_05: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_06: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_06: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_07: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_07: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_08: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_08: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_09: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_09: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_10: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_10: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_11: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_11: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_12: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_12: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_13: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_13: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_14: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_14: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_15: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_15: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_16: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_16: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_17: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_17: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_18: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_18: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_19: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_19: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_20: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_20: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_21: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_21: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_22: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_22: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_23: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_23: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_24: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_24: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_25: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_25: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2_26: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L2.
L3_26: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: L3.
L2: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: potential_prefix.
L3: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: sequence_lower_bound.
grid: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: IsTwoDominating, cols_feasible, column_reduction, grid_neighbor_sum, lower_bound.
IsTwoDominating: proof_shape: bind-only; escape_witness: none; frozen=F; consumers: cols_feasible, column_reduction, gamma2, lower_bound, result, three_column_reduction, upper_dominating.
gamma2: proof_shape: bind-only; escape_witness: none; frozen=F; consumers: claim, result.
claim: proof_shape: bind-only; escape_witness: none; frozen=F; consumers: result.
pad: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: pad_apply, cols, cols_digits, cols_end, cols_zero, column_reduction, grid_neighbor_sum, pad_bound, pad_end, pad_succ, pad_upper_f, three_column_reduction, upper_dominating, weight_columns.
pad_apply: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: pad_succ, pad_end, grid_neighbor_sum, pad_bound, cols_zero, pad_upper_f.
pad_succ: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: column_reduction, weight_columns.
pad_end: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: cols_end.
path_neighbor_sum: proof_shape: bind-only; escape_witness: none; frozen=F; consumers: columnA_three, grid_neighbor_sum.
grid_neighbor_sum: proof_shape: bind-only; escape_witness: none; frozen=F; consumers: column_reduction.
ColumnA: proof_shape: bind-only; escape_witness: none; frozen=F; consumers: columnA_digit, columnA_three, column_reduction, three_column_reduction, upper_dominating.
column_reduction: proof_shape: bind-only; escape_witness: none; frozen=F; consumers: three_column_reduction, upper_dominating.
pack: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: cols, pack_digits.
pack_digits: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: cols_digits.
pad_bound: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: cols, cols_digits, cols_end, cols_zero.
cols: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: cols_digits, cols_end, cols_feasible, cols_zero, lower_bound, three_column_reduction, weight_columns.
cols_digits: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: three_column_reduction, weight_columns.
cols_zero: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: lower_bound.
cols_end: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: lower_bound.
columnA_three: proof_shape: bind-only; escape_witness: none; frozen=F; consumers: columnA_digit, three_column_reduction.
three_column_reduction: proof_shape: bind-only; escape_witness: none; frozen=F; consumers: cols_feasible.
cols_feasible: proof_shape: bind-only; escape_witness: none; frozen=F; consumers: lower_bound.
potential_prefix: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: sequence_lower_bound.
sequence_lower_bound: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: lower_bound.
digit: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: columnA_digit, digit_bound, digit_sum, pad_upper_f, upper_dominating, upper_f, upper_weight, weight_columns.
digit_sum: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: upper_weight, weight_columns.
weight_columns: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: lower_bound.
lower_bound: proof_shape: bind-only; escape_witness: none; frozen=F; consumers: result.
uc: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: pad_upper_f, s_uc_formula, sum_uc, uc_feasible, upper_dominating, upper_f, upper_weight.
uc_feasible: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: upper_dominating.
digit_bound: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: upper_dominating.
columnA_digit: proof_shape: bind-only; escape_witness: none; frozen=F; consumers: upper_dominating.
upper_f: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: pad_upper_f, result, upper_dominating, upper_weight.
pad_upper_f: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: upper_dominating.
upper_dominating: proof_shape: bind-only; escape_witness: none; frozen=F; consumers: result.
alternating_sum: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: sum_uc.
s_uc_formula: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: sum_uc.
sum_uc: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: upper_weight.
upper_weight: proof_shape: bind-only; escape_witness: none; frozen=none; consumers: result.
result: proof_shape: bind-only; escape_witness: none; frozen=F; consumers: external settling result.
-/
import Mathlib.Algebra.BigOperators.Fin
import D5.S1.Digit.MaxDigitSumBase
import D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace D5.S3.Combinatorics.Graph.Domination.LeeLiuThreeRowIntegerDomination

open SimpleGraph
open scoped BigOperators

private def s (a : Fin 27) : ℕ := D5.S1.Digit.MaxDigitSumBase.digitSum 3 a.val
private def A (a b c : Fin 27) : Prop :=
  2 ≤ (a.val / 9) + ((b.val / 9) + (b.val / 3 % 3)) + (c.val / 9) ∧
  2 ≤ (a.val / 3 % 3) + ((b.val / 9) + (b.val / 3 % 3) + (b.val % 3)) + (c.val / 3 % 3) ∧
  2 ≤ (a.val % 3) + ((b.val / 3 % 3) + (b.val % 3)) + (c.val % 3)
private instance aDecidable (a b c : Fin 27) : Decidable (A a b c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private def R (a b : Fin 27) : ℤ :=
  match a.val with
  | 0 => match b.val with
    | 14 | 17 | 20 | 22 | 23 | 25 => -5
    | 7 | 8 | 11 | 13 | 15 | 16 | 19 | 24 => -4
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 9 | 10 | 12 | 18 | 21 => -3
    | _ => -6
  | 1 => match b.val with
    | 4 | 5 | 7 | 8 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 21 | 24 => -5
    | 3 | 6 | 9 => -4
    | 0 | 1 | 2 => -3
    | _ => -6
  | 2 => match b.val with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => -5
    | _ => -6
  | 3 => match b.val with
    | 1 | 2 | 4 | 5 | 7 | 8 | 9 | 10 | 11 | 12 | 15 | 18 | 19 | 20 | 21 | 24 => -5
    | 0 | 3 | 6 => -4
    | _ => -6
  | 4 => -6
  | 5 => -6
  | 6 => -6
  | 7 => -7
  | 8 => -7
  | 9 => match b.val with
    | 2 | 4 | 5 | 7 | 8 | 10 | 12 | 13 | 15 | 16 | 19 | 21 | 22 | 24 | 25 => -5
    | 1 | 3 | 6 => -4
    | 0 | 9 | 18 => -3
    | _ => -6
  | 10 => match b.val with
    | 0 | 3 | 6 => -5
    | _ => -6
  | 11 => -7
  | 12 => -6
  | 13 => -7
  | 14 => -8
  | 15 => -7
  | 16 => -7
  | 17 => -8
  | 18 => match b.val with
    | 0 | 3 | 6 | 9 | 12 | 15 | 18 | 21 | 24 => -5
    | _ => -6
  | 19 => -7
  | 20 => -8
  | 21 => -6
  | 22 => -8
  | 23 => -8
  | 24 => -7
  | 25 => -8
  | _ => -9
private def Phi (a b : Fin 27) : ℤ := 2 * (s a : ℤ) + 2 * (s b : ℤ) + R a b

private theorem L1 : ∀ b : Fin 27, Phi 0 b ≤ 2 * (s b : ℤ) - 3 := by decide

private theorem L2_00 : ∀ b c : Fin 27, A 0 b c →
    Phi b c ≤ Phi 0 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_00 : ∀ b : Fin 27, A 0 b 0 → 1 ≤ Phi 0 b := by decide

private theorem L2_01 : ∀ b c : Fin 27, A 1 b c →
    Phi b c ≤ Phi 1 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_01 : ∀ b : Fin 27, A 1 b 0 → 1 ≤ Phi 1 b := by decide

private theorem L2_02 : ∀ b c : Fin 27, A 2 b c →
    Phi b c ≤ Phi 2 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_02 : ∀ b : Fin 27, A 2 b 0 → 1 ≤ Phi 2 b := by decide

private theorem L2_03 : ∀ b c : Fin 27, A 3 b c →
    Phi b c ≤ Phi 3 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_03 : ∀ b : Fin 27, A 3 b 0 → 1 ≤ Phi 3 b := by decide

private theorem L2_04 : ∀ b c : Fin 27, A 4 b c →
    Phi b c ≤ Phi 4 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_04 : ∀ b : Fin 27, A 4 b 0 → 1 ≤ Phi 4 b := by decide

private theorem L2_05 : ∀ b c : Fin 27, A 5 b c →
    Phi b c ≤ Phi 5 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_05 : ∀ b : Fin 27, A 5 b 0 → 1 ≤ Phi 5 b := by decide

private theorem L2_06 : ∀ b c : Fin 27, A 6 b c →
    Phi b c ≤ Phi 6 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_06 : ∀ b : Fin 27, A 6 b 0 → 1 ≤ Phi 6 b := by decide

private theorem L2_07 : ∀ b c : Fin 27, A 7 b c →
    Phi b c ≤ Phi 7 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_07 : ∀ b : Fin 27, A 7 b 0 → 1 ≤ Phi 7 b := by decide

private theorem L2_08 : ∀ b c : Fin 27, A 8 b c →
    Phi b c ≤ Phi 8 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_08 : ∀ b : Fin 27, A 8 b 0 → 1 ≤ Phi 8 b := by decide

private theorem L2_09 : ∀ b c : Fin 27, A 9 b c →
    Phi b c ≤ Phi 9 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_09 : ∀ b : Fin 27, A 9 b 0 → 1 ≤ Phi 9 b := by decide

private theorem L2_10 : ∀ b c : Fin 27, A 10 b c →
    Phi b c ≤ Phi 10 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_10 : ∀ b : Fin 27, A 10 b 0 → 1 ≤ Phi 10 b := by decide

private theorem L2_11 : ∀ b c : Fin 27, A 11 b c →
    Phi b c ≤ Phi 11 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_11 : ∀ b : Fin 27, A 11 b 0 → 1 ≤ Phi 11 b := by decide

private theorem L2_12 : ∀ b c : Fin 27, A 12 b c →
    Phi b c ≤ Phi 12 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_12 : ∀ b : Fin 27, A 12 b 0 → 1 ≤ Phi 12 b := by decide

private theorem L2_13 : ∀ b c : Fin 27, A 13 b c →
    Phi b c ≤ Phi 13 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_13 : ∀ b : Fin 27, A 13 b 0 → 1 ≤ Phi 13 b := by decide

private theorem L2_14 : ∀ b c : Fin 27, A 14 b c →
    Phi b c ≤ Phi 14 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_14 : ∀ b : Fin 27, A 14 b 0 → 1 ≤ Phi 14 b := by decide

private theorem L2_15 : ∀ b c : Fin 27, A 15 b c →
    Phi b c ≤ Phi 15 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_15 : ∀ b : Fin 27, A 15 b 0 → 1 ≤ Phi 15 b := by decide

private theorem L2_16 : ∀ b c : Fin 27, A 16 b c →
    Phi b c ≤ Phi 16 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_16 : ∀ b : Fin 27, A 16 b 0 → 1 ≤ Phi 16 b := by decide

private theorem L2_17 : ∀ b c : Fin 27, A 17 b c →
    Phi b c ≤ Phi 17 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_17 : ∀ b : Fin 27, A 17 b 0 → 1 ≤ Phi 17 b := by decide

private theorem L2_18 : ∀ b c : Fin 27, A 18 b c →
    Phi b c ≤ Phi 18 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_18 : ∀ b : Fin 27, A 18 b 0 → 1 ≤ Phi 18 b := by decide

private theorem L2_19 : ∀ b c : Fin 27, A 19 b c →
    Phi b c ≤ Phi 19 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_19 : ∀ b : Fin 27, A 19 b 0 → 1 ≤ Phi 19 b := by decide

private theorem L2_20 : ∀ b c : Fin 27, A 20 b c →
    Phi b c ≤ Phi 20 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_20 : ∀ b : Fin 27, A 20 b 0 → 1 ≤ Phi 20 b := by decide

private theorem L2_21 : ∀ b c : Fin 27, A 21 b c →
    Phi b c ≤ Phi 21 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_21 : ∀ b : Fin 27, A 21 b 0 → 1 ≤ Phi 21 b := by decide

private theorem L2_22 : ∀ b c : Fin 27, A 22 b c →
    Phi b c ≤ Phi 22 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_22 : ∀ b : Fin 27, A 22 b 0 → 1 ≤ Phi 22 b := by decide

private theorem L2_23 : ∀ b c : Fin 27, A 23 b c →
    Phi b c ≤ Phi 23 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_23 : ∀ b : Fin 27, A 23 b 0 → 1 ≤ Phi 23 b := by decide

private theorem L2_24 : ∀ b c : Fin 27, A 24 b c →
    Phi b c ≤ Phi 24 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_24 : ∀ b : Fin 27, A 24 b 0 → 1 ≤ Phi 24 b := by decide

private theorem L2_25 : ∀ b c : Fin 27, A 25 b c →
    Phi b c ≤ Phi 25 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_25 : ∀ b : Fin 27, A 25 b 0 → 1 ≤ Phi 25 b := by decide

private theorem L2_26 : ∀ b c : Fin 27, A 26 b c →
    Phi b c ≤ Phi 26 b + 2 * (s c : ℤ) - 3 := by decide
private theorem L3_26 : ∀ b : Fin 27, A 26 b 0 → 1 ≤ Phi 26 b := by decide


private theorem L2 (a b c : Fin 27) (h : A a b c) : Phi b c ≤ Phi a b + 2 * (s c : ℤ) - 3 := by
  fin_cases a
  · exact L2_00 b c h
  · exact L2_01 b c h
  · exact L2_02 b c h
  · exact L2_03 b c h
  · exact L2_04 b c h
  · exact L2_05 b c h
  · exact L2_06 b c h
  · exact L2_07 b c h
  · exact L2_08 b c h
  · exact L2_09 b c h
  · exact L2_10 b c h
  · exact L2_11 b c h
  · exact L2_12 b c h
  · exact L2_13 b c h
  · exact L2_14 b c h
  · exact L2_15 b c h
  · exact L2_16 b c h
  · exact L2_17 b c h
  · exact L2_18 b c h
  · exact L2_19 b c h
  · exact L2_20 b c h
  · exact L2_21 b c h
  · exact L2_22 b c h
  · exact L2_23 b c h
  · exact L2_24 b c h
  · exact L2_25 b c h
  · exact L2_26 b c h

private theorem L3 (a b : Fin 27) (h : A a b 0) : 1 ≤ Phi a b := by
  fin_cases a
  · exact L3_00 b h
  · exact L3_01 b h
  · exact L3_02 b h
  · exact L3_03 b h
  · exact L3_04 b h
  · exact L3_05 b h
  · exact L3_06 b h
  · exact L3_07 b h
  · exact L3_08 b h
  · exact L3_09 b h
  · exact L3_10 b h
  · exact L3_11 b h
  · exact L3_12 b h
  · exact L3_13 b h
  · exact L3_14 b h
  · exact L3_15 b h
  · exact L3_16 b h
  · exact L3_17 b h
  · exact L3_18 b h
  · exact L3_19 b h
  · exact L3_20 b h
  · exact L3_21 b h
  · exact L3_22 b h
  · exact L3_23 b h
  · exact L3_24 b h
  · exact L3_25 b h
  · exact L3_26 b h






/-- The grid graph `G_{m,n} = P_m □ P_n` (Cartesian product of paths). -/
abbrev grid (m n : ℕ) : SimpleGraph (Fin m × Fin n) := pathGraph m □ pathGraph n

/-- An integer {2}-dominating function of `G_{m,n}`: values in `{0,1,2}`, and the sum over
every closed neighbourhood `N[v]` is at least `2`. -/
def IsTwoDominating (m n : ℕ) (f : Fin m × Fin n → ℕ) : Prop :=
  (∀ v, f v ≤ 2) ∧ ∀ v, 2 ≤ f v + ∑ u ∈ (grid m n).neighborFinset v, f u

/-- The integer {2}-domination number `γ_{2}(G_{m,n})`: the minimum weight of an integer
{2}-dominating function. -/
noncomputable def gamma2 (m n : ℕ) : ℕ :=
  sInf {w | ∃ f, IsTwoDominating m n f ∧ ∑ v, f v = w}

/-- Lee–Liu, Conjecture 2.5: `γ_{2}(G_{3,n}) = ⌊3n/2⌋ + 1` for every positive integer `n`. -/
def claim : Prop := ∀ n : ℕ, 1 ≤ n → gamma2 3 n = 3 * n / 2 + 1


noncomputable def pad {m n : ℕ} (f : Fin m × Fin n → ℕ) (k : ℕ)
    (i : Fin m) : ℕ :=
  Function.extend (fun j : Fin n => j.val + 1) (fun j => f (i,j)) (fun _ => 0) k

private theorem pad_apply {m n : ℕ} (f : Fin m × Fin n → ℕ) (k : ℕ) (i : Fin m) :
    pad f k i = if h : 0 < k ∧ k ≤ n then f (i, ⟨k-1, by omega⟩) else 0 := by
  classical
  unfold pad
  by_cases hk : 0 < k ∧ k ≤ n
  · rw [dite_eq_left hk]
    have hi : Function.Injective (fun j : Fin n => j.val + 1) :=
      Nat.succ_injective.comp Fin.val_injective
    have he := hi.extend_apply (fun j => f (i,j)) (fun _ => 0) ⟨k-1, by omega⟩
    simpa only [Nat.sub_add_cancel hk.1] using he
  · rw [dite_eq_right hk]
    apply Function.extend_apply'
    rintro ⟨j, hj⟩
    apply hk
    constructor
    · rw [← hj]
      exact Nat.zero_lt_succ _
    · rw [← hj]
      exact Nat.succ_le_of_lt j.isLt

private theorem pad_succ {m n : ℕ} (f : Fin m × Fin n → ℕ) (j : Fin n) (i : Fin m) :
    pad f (j.val + 1) i = f (i,j) := by
  simp [pad_apply, j.isLt]

private theorem pad_end {m n : ℕ} (f : Fin m × Fin n → ℕ) : pad f (n + 1) = fun _ => 0 := by
  funext i
  simp [pad_apply]

private theorem path_neighbor_sum {n : ℕ} (f : Fin n → ℕ) (j : Fin n) :
    ∑ k ∈ (pathGraph n).neighborFinset j, f k =
      (if h : 0 < j.val then f ⟨j.val - 1, by omega⟩ else 0) +
      (if h : j.val + 1 < n then f ⟨j.val + 1, h⟩ else 0) := by
  classical
  by_cases hl : 0 < j.val <;> by_cases hr : j.val + 1 < n
  · have he : (pathGraph n).neighborFinset j = {⟨j.val - 1, by omega⟩, ⟨j.val + 1, hr⟩} := by
      ext k
      simp only [mem_neighborFinset, pathGraph_adj, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      omega
    rw [he]
    simp [hl, hr, show (⟨j.val - 1, by omega⟩ : Fin n) ≠ ⟨j.val + 1, hr⟩ by
      intro hne; have hv := congrArg Fin.val hne; simp only at hv; omega]
  · have he : (pathGraph n).neighborFinset j = {⟨j.val - 1, by omega⟩} := by
      ext k
      simp only [mem_neighborFinset, pathGraph_adj, Finset.mem_singleton, Fin.ext_iff]
      omega
    simp [he, hl, hr]
  · have he : (pathGraph n).neighborFinset j = {⟨j.val + 1, hr⟩} := by
      ext k
      simp only [mem_neighborFinset, pathGraph_adj, Finset.mem_singleton, Fin.ext_iff]
      omega
    simp [he, hl, hr]
  · have he : (pathGraph n).neighborFinset j = ∅ := by
      ext k
      simp only [mem_neighborFinset, pathGraph_adj, Finset.notMem_empty, iff_false, not_or]
      constructor <;> omega
    simp [he, hl, hr]

private theorem grid_neighbor_sum {m n : ℕ} (f : Fin m × Fin n → ℕ) (i : Fin m) (j : Fin n) :
    ∑ v ∈ (grid m n).neighborFinset (i,j), f v =
      (∑ k ∈ (pathGraph m).neighborFinset i, f (k,j)) + pad f j.val i + pad f (j.val + 2) i := by
  classical
  change ∑ v ∈ (pathGraph m □ pathGraph n).neighborFinset (i,j), f v = _
  rw [neighborFinset_boxProd, Finset.sum_disjUnion]
  simp only [Finset.sum_product, Finset.sum_singleton]
  rw [path_neighbor_sum (fun k => f (i,k)) j]
  by_cases hl : 0 < j.val <;> by_cases hr : j.val + 1 < n <;>
    simp [pad_apply, hl, hr, Nat.add_assoc, Nat.zero_lt_succ (j.val + 1),
      show (j.val + 2 ≤ n ↔ j.val + 1 < n) from Nat.add_one_le_iff]

def ColumnA (m : ℕ) (a b c : Fin m → ℕ) : Prop :=
  ∀ i, 2 ≤ b i + (∑ k ∈ (pathGraph m).neighborFinset i, b k) + a i + c i

theorem column_reduction {m n : ℕ} (f : Fin m × Fin n → ℕ) (hb : ∀ v, f v ≤ 2) :
    IsTwoDominating m n f ↔
      ∀ j : Fin n, ColumnA m (pad f j.val) (pad f (j.val + 1)) (pad f (j.val + 2)) := by
  constructor
  · intro h j i
    have hv := h.2 (i,j)
    rw [grid_neighbor_sum] at hv
    simp only [pad_succ]
    omega
  · intro h
    refine ⟨hb, ?_⟩
    intro v
    obtain ⟨i,j⟩ := v
    have hv := h j i
    simp only [pad_succ] at hv
    rw [grid_neighbor_sum]
    omega


private def pack (a b c : ℕ) (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2) : Fin 27 :=
  finProdFinEquiv ((⟨a, Nat.lt_succ_of_le ha⟩ : Fin 3),
    finProdFinEquiv ((⟨b, Nat.lt_succ_of_le hb⟩ : Fin 3),
      (⟨c, Nat.lt_succ_of_le hc⟩ : Fin 3)))

private theorem pack_digits (a b c : ℕ) (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2) :
    ((pack a b c ha hb hc).val / 9) = a ∧ ((pack a b c ha hb hc).val / 3 % 3) = b ∧
    ((pack a b c ha hb hc).val % 3) = c := by
  simp only [pack, finProdFinEquiv, Equiv.coe_fn_mk]
  omega

private theorem pad_bound {m n : ℕ} (f : Fin m × Fin n → ℕ) (hb : ∀ v, f v ≤ 2)
    (k : ℕ) (i : Fin m) : pad f k i ≤ 2 := by
  rw [pad_apply]
  split
  · exact hb _
  · omega

private noncomputable def cols {n : ℕ} (f : Fin 3 × Fin n → ℕ) (hb : ∀ v, f v ≤ 2) (k : ℕ) : Fin 27 :=
  pack (pad f k 0) (pad f k 1) (pad f k 2)
    (pad_bound f hb k 0) (pad_bound f hb k 1) (pad_bound f hb k 2)

private theorem cols_digits {n : ℕ} (f : Fin 3 × Fin n → ℕ) (hb : ∀ v, f v ≤ 2) (k : ℕ) :
    ((cols f hb k).val / 9) = pad f k 0 ∧ ((cols f hb k).val / 3 % 3) = pad f k 1 ∧
    ((cols f hb k).val % 3) = pad f k 2 := by
  exact pack_digits _ _ _ _ _ _

private theorem cols_zero {n : ℕ} (f : Fin 3 × Fin n → ℕ) (hb : ∀ v, f v ≤ 2) :
    cols f hb 0 = 0 := by
  apply Fin.eq_of_val_eq
  simp [cols, pack, finProdFinEquiv, pad_apply]

private theorem cols_end {n : ℕ} (f : Fin 3 × Fin n → ℕ) (hb : ∀ v, f v ≤ 2) :
    cols f hb (n + 1) = 0 := by
  apply Fin.ext
  simp [cols, pack, finProdFinEquiv, pad_end]

private theorem columnA_three (a b c : Fin 3 → ℕ) : ColumnA 3 a b c ↔
    (2 ≤ a 0 + (b 0 + b 1) + c 0 ∧
     2 ≤ a 1 + (b 0 + b 1 + b 2) + c 1 ∧
     2 ≤ a 2 + (b 1 + b 2) + c 2) := by
  simp only [ColumnA, path_neighbor_sum, Fin.forall_fin_succ]
  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] <;> omega

private theorem three_column_reduction {n : ℕ} (f : Fin 3 × Fin n → ℕ) (hb : ∀ v, f v ≤ 2) :
    IsTwoDominating 3 n f ↔ ∀ j : Fin n,
      A (cols f hb j.val) (cols f hb (j.val+1)) (cols f hb (j.val+2)) := by
  rw [column_reduction f hb]
  apply forall_congr'
  intro j
  rw [columnA_three]
  rcases cols_digits f hb j.val with ⟨h00,h01,h02⟩
  rcases cols_digits f hb (j.val+1) with ⟨h10,h11,h12⟩
  rcases cols_digits f hb (j.val+2) with ⟨h20,h21,h22⟩
  simp only [A,h00,h01,h02,h10,h11,h12,h20,h21,h22]

private theorem cols_feasible {n : ℕ} (f : Fin 3 × Fin n → ℕ) (hf : IsTwoDominating 3 n f)
    (j : ℕ) (hj : j < n) : A (cols f hf.1 j) (cols f hf.1 (j+1)) (cols f hf.1 (j+2)) := by
  exact ((three_column_reduction f hf.1).mp hf) ⟨j,hj⟩

private theorem potential_prefix (n : ℕ) (x : ℕ → Fin 27) (h0 : x 0 = 0)
    (hA : ∀ j < n, A (x j) (x (j+1)) (x (j+2))) :
    ∀ k, 1 ≤ k → k ≤ n →
      Phi (x (k-1)) (x k) ≤ 2 * ((∑ i ∈ Finset.range k, s (x (i+1)) : ℕ) : ℤ) - 3 * k := by
  intro k hk hkn
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  have hs : (∑ i ∈ Finset.range t,
      (Phi (x (i+1)) (x (i+2)) - Phi (x i) (x (i+1)))) ≤
      ∑ i ∈ Finset.range t, (2 * (s (x (i+2)) : ℤ) - 3) := by
    apply Finset.sum_le_sum
    intro i hi
    have hstep : Phi (x (i+1)) (x (i+2)) ≤
        Phi (x i) (x (i+1)) + 2 * (s (x (i+2)) : ℤ) - 3 :=
      L2 (x i) (x (i+1)) (x (i+2))
        (hA i (lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.le_of_succ_le hkn)))
    omega
  have htel := Finset.sum_range_sub (fun i => Phi (x i) (x (i+1))) t
  have hsum : (((∑ i ∈ Finset.range (t+1), s (x (i+1))) : ℕ) : ℤ) =
      (s (x 1) : ℤ) + ∑ i ∈ Finset.range t, (s (x (i+2)) : ℤ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_sum, Nat.zero_add, Nat.add_assoc]
    exact add_comm _ _
  have hinit := L1 (x 1)
  rw [← h0] at hinit
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [htel] at hs
  simp only [Nat.zero_add] at hs
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hs
  omega


private theorem sequence_lower_bound (n : ℕ) (hn : 1 ≤ n) (x : ℕ → Fin 27)
    (h0 : x 0 = 0) (hend : x (n+1) = 0)
    (hA : ∀ j < n, A (x j) (x (j+1)) (x (j+2))) :
    3 * n / 2 + 1 ≤ ∑ i ∈ Finset.range n, s (x (i+1)) := by
  have hp := potential_prefix n x h0 hA n hn le_rfl
  have ha := hA (n-1) (Nat.sub_one_lt_of_lt hn)
  have he1 : n-1+1 = n := Nat.sub_add_cancel hn
  have he2 : n-1+2 = n+1 := by
    simpa only [Nat.add_assoc] using congrArg (fun x : ℕ => x + 1) he1
  rw [he1, he2, hend] at ha
  have ht := L3 (x (n-1)) (x n) ha
  omega


private def digit (a : Fin 27) (i : Fin 3) : ℕ :=
  ((finFunctionFinEquiv.symm a : Fin 3 → Fin 3) i.rev).val


private theorem digit_sum (a : Fin 27) : ∑ i : Fin 3, digit a i = s a := by
  have hs : s = fun a : Fin 27 => (a.val / 9) + (a.val / 3 % 3) + (a.val % 3) := by
    funext a
    fin_cases a <;> decide
  have hd : digit = fun a : Fin 27 => fun i : Fin 3 =>
      if i = 0 then (a.val / 9) else if i = 1 then (a.val / 3 % 3) else (a.val % 3) := by
    funext a i
    fin_cases i <;> fin_cases a <;> decide
  simp [Fin.sum_univ_succ, hd, hs, Nat.add_assoc]


private theorem weight_columns {n : ℕ} (f : Fin 3 × Fin n → ℕ) (hb : ∀ v, f v ≤ 2) :
    ∑ v, f v = ∑ j ∈ Finset.range n, s (cols f hb (j+1)) := by
  have hs (j : Fin n) : s (cols f hb (j.val+1)) = ∑ i : Fin 3, f (i,j) := by
    rcases cols_digits f hb (j.val+1) with ⟨h0,h1,h2⟩
    rw [← digit_sum]
    have hd : digit = fun a : Fin 27 => fun i : Fin 3 =>
        if i = 0 then (a.val / 9) else if i = 1 then (a.val / 3 % 3) else (a.val % 3) := by
      funext a i
      fin_cases i <;> fin_cases a <;> decide
    simp [hd, h0, h1, h2, pad_succ, Fin.sum_univ_succ]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [← hs]
  exact Fin.sum_univ_eq_sum_range (fun j => s (cols f hb (j+1))) n


private theorem lower_bound {n : ℕ} (hn : 1 ≤ n) (f : Fin 3 × Fin n → ℕ)
    (hf : IsTwoDominating 3 n f) : 3 * n / 2 + 1 ≤ ∑ v, f v := by
  rw [weight_columns f hf.1]
  exact sequence_lower_bound n hn (cols f hf.1) (cols_zero f hf.1) (cols_end f hf.1)
    (fun j hj => cols_feasible f hf j hj)


private def uc (n k : ℕ) : Fin 27 :=
  if k = 0 ∨ n < k then 0 else
  if n = 1 then 6 else
  if k % 2 = 0 then 13 else
  if k = 1 ∨ k = n then 3 else 0


private theorem uc_feasible (n j : ℕ) (hj : j < n) : A (uc n j) (uc n (j+1)) (uc n (j+2)) := by
  by_cases hn : n = 1
  · subst n
    have : j = 0 := Nat.lt_one_iff.mp hj
    subst j
    decide
  · have hin (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) : uc n k =
        if k % 2 = 0 then 13 else if k = 1 ∨ k = n then 3 else 0 := by
      simp [uc, hn, show ¬(k = 0 ∨ n < k) by omega]
    by_cases he : (j+1) % 2 = 0
    · rw [hin (j+1) (Nat.le_add_left 1 j) (Nat.succ_le_of_lt hj), if_pos he]
      change 2 ≤ ((uc n j).val / 9) + 2 + ((uc n (j+2)).val / 9) ∧
        2 ≤ ((uc n j).val / 3 % 3) + 3 + ((uc n (j+2)).val / 3 % 3) ∧
        2 ≤ ((uc n j).val % 3) + 2 + ((uc n (j+2)).val % 3)
      omega
    · have hjpar : j % 2 = 0 := by omega
      have hj2par : (j+2) % 2 = 0 := by omega
      by_cases hj0 : j = 0
      · subst j
        have hn2 : 2 ≤ n := by omega
        have hz : uc n 0 = 0 := Fin.eq_of_val_eq rfl
        rw [hz, hin 1 le_rfl (Nat.one_le_of_lt hj), hin 2 (by exact NeZero.one_le) hn2]
        norm_num [A]
      · by_cases hlast : j+1 = n
        · have hz : uc n (j+2) = 0 := by simp [uc, show n < j+2 by omega]
          rw [hin j (Nat.one_le_iff_ne_zero.mpr hj0) (Nat.le_of_lt hj),
            hin (j+1) (Nat.le_add_left 1 j) (Nat.succ_le_of_lt hj), hz]
          have hnodd : n % 2 ≠ 0 := by simpa only [hlast] using he
          simp [hjpar, hlast, hnodd, A]
        · rw [hin j (Nat.one_le_iff_ne_zero.mpr hj0) (Nat.le_of_lt hj),
            hin (j+1) (Nat.le_add_left 1 j) (Nat.succ_le_of_lt hj),
            hin (j+2) (Nat.le_add_left 1 (j+1)) (by omega)]
          simp [hjpar, he, hj2par, hlast, A]


private theorem digit_bound (a : Fin 27) (i : Fin 3) : digit a i ≤ 2 := by
  exact Nat.le_of_lt_succ ((finFunctionFinEquiv.symm a : Fin 3 → Fin 3) i.rev).isLt

private theorem columnA_digit (a b c : Fin 27) : ColumnA 3 (digit a) (digit b) (digit c) ↔ A a b c := by
  rw [columnA_three]
  have hd : digit = fun a : Fin 27 => fun i : Fin 3 =>
      if i = 0 then (a.val / 9) else if i = 1 then (a.val / 3 % 3) else (a.val % 3) := by
    funext a i
    fin_cases i <;> fin_cases a <;> decide
  simp [hd, A]

private def upper_f (n : ℕ) (v : Fin 3 × Fin n) : ℕ := digit (uc n (v.2.val + 1)) v.1

private theorem pad_upper_f (n k : ℕ) : pad (upper_f n) k = digit (uc n k) := by
  funext i
  by_cases hk : 0 < k ∧ k ≤ n
  · simp [pad_apply, hk, upper_f, Nat.sub_add_cancel hk.1]
  · have hbad : k = 0 ∨ n < k := by omega
    have hd : digit = fun a : Fin 27 => fun i : Fin 3 =>
        if i = 0 then (a.val / 9) else if i = 1 then (a.val / 3 % 3) else (a.val % 3) := by
      funext a i
      fin_cases i <;> fin_cases a <;> decide
    simp [pad_apply, hk, uc, hbad, hd]

private theorem upper_dominating (n : ℕ) : IsTwoDominating 3 n (upper_f n) := by
  apply (column_reduction _ (fun v => digit_bound _ _)).mpr
  intro j
  change ColumnA 3 (pad (upper_f n) j.val) (pad (upper_f n) (j.val+1)) (pad (upper_f n) (j.val+2))
  simp only [pad_upper_f]
  exact (columnA_digit _ _ _).mpr (uc_feasible n j.val j.isLt)


private theorem alternating_sum (n : ℕ) :
    ∑ j ∈ Finset.range n, (if (j+1) % 2 = 0 then 3 else 0) = 3 * (n / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

private theorem s_uc_formula (n j : ℕ) (hn : 1 ≤ n) (hj : j < n) :
    s (uc n (j+1)) = (if (j+1) % 2 = 0 then 3 else 0) +
      (if j = 0 then 1 else 0) + (if j+1 = n ∧ n % 2 = 1 then 1 else 0) := by
  have hs : s = fun a : Fin 27 => (a.val / 9) + (a.val / 3 % 3) + (a.val % 3) := by
    funext a
    fin_cases a <;> decide
  by_cases hn1 : n = 1
  · subst n
    have hj0 : j = 0 := Nat.lt_one_iff.mp hj
    subst j
    decide
  · have hgood : ¬(j+1 = 0 ∨ n < j+1) := by omega
    simp only [uc, hgood, if_false, hn1]
    by_cases he : (j+1) % 2 = 0
    · have hj0 : j ≠ 0 := by omega
      have hfinal : ¬(j+1 = n ∧ n % 2 = 1) := by omega
      simp [he, hj0, hfinal, hs]
    · by_cases hj0 : j = 0 <;> by_cases hfinal : j+1 = n <;>
        simp_all [hs]

private theorem sum_uc (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range n, s (uc n (j+1)) = 3 * n / 2 + 1 := by
  have hf : (∑ j ∈ Finset.range n, s (uc n (j+1))) =
      (∑ j ∈ Finset.range n, (if (j+1) % 2 = 0 then 3 else 0)) +
      (∑ j ∈ Finset.range n, (if j = 0 then 1 else 0)) +
      (∑ j ∈ Finset.range n, (if j+1 = n ∧ n % 2 = 1 then 1 else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact s_uc_formula n j hn (Finset.mem_range.mp hj)
  rw [hf, alternating_sum]
  have hs : (∑ j ∈ Finset.range n, (if j = 0 then 1 else 0)) = 1 := by
    simp [Nat.ne_zero_of_lt hn]
  rw [hs]
  have ht : (∑ j ∈ Finset.range n, (if j+1 = n ∧ n % 2 = 1 then 1 else 0)) =
      if n % 2 = 1 then 1 else 0 := by
    have he (j : ℕ) : (j+1 = n ∧ n % 2 = 1) ↔ (j = n-1 ∧ n % 2 = 1) := by omega
    simp_rw [he]
    by_cases hp : n % 2 = 1 <;> simp [hp, Nat.sub_one_lt_of_lt hn]
  rw [ht]
  split_ifs <;> omega


private theorem upper_weight (n : ℕ) (hn : 1 ≤ n) : ∑ v, upper_f n v = 3 * n / 2 + 1 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [upper_f, digit_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j => s (uc n (j+1))) n]
  exact sum_uc n hn


theorem result : claim := by
  intro n hn
  have hu := upper_dominating n
  have hw := upper_weight n hn
  have hmem : 3 * n / 2 + 1 ∈ {w | ∃ f, IsTwoDominating 3 n f ∧ ∑ v, f v = w} :=
    ⟨upper_f n, hu, hw⟩
  unfold gamma2
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨_, hmem⟩
  rintro w ⟨f, hf, rfl⟩
  exact lower_bound hn f hf



end D5.S3.Combinatorics.Graph.Domination.LeeLiuThreeRowIntegerDomination
