/- GID: D5/S1/Words/EvilOdious/SequenceCoefficients
   generality: I
   mirror-B: D5/B/S1/Words/EvilOdious/SequenceCoefficients
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Sixfold Thue-Morse counts are controlled by dyadic coefficient states. -/

/-
admission_basis: escape-witness
Module escape_witness: recur_eq_coeff
Direct frozen dependencies: aliases below denote declaration identities, not module pins.
T0 = D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.thueMorse
  statement_id: sha256:64e3518f7565865a40ea42fed02d3ec99a43a5957584903476dff7ab488bd8b0
T2 = D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.thueMorse_two_mul
  statement_id: sha256:bf55640ac023e7929642cb19d30dba7694cf92e3200ef026c879f77a1293cbca
T3 = D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.thueMorse_two_mul_add_one
  statement_id: sha256:d2a4385c4493b662cbf5172983c049e669dd2404058476ba99c3a7b487ac5009
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15228.
Declaration rows: name | proof_shape | frozen dependencies | escape_witness | consumers.
Definitions carry bind-only as an organization label; no proof content is claimed for them.
r | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SixfoldMonotonicity.initial_r, SixfoldMonotonicity.r_strict, SixfoldMonotonicity.claim, SixfoldMonotonicity.result, SequenceCoefficients.coeff_E, SequenceCoefficients.r_difference_coeff, SequenceCoefficients.r_difference
s | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SixfoldMonotonicity.initial_s, SixfoldMonotonicity.s_strict, SixfoldMonotonicity.claim, SixfoldMonotonicity.result, SequenceCoefficients.coeff_O, SequenceCoefficients.s_difference_coeff, SequenceCoefficients.s_difference
E | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.two_E, SequenceCoefficients.coeff_E, SequenceCoefficients.r_difference_coeff
O | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.two_O, SequenceCoefficients.coeff_O, SequenceCoefficients.s_difference_coeff
T | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.two_E, SequenceCoefficients.two_O, SequenceCoefficients.T_functional, SequenceCoefficients.H, SequenceCoefficients.H_functional, SequenceCoefficients.C_functional, SequenceCoefficients.difference_series, SequenceCoefficients.r_difference_coeff, SequenceCoefficients.s_difference_coeff, SequenceCoefficients.c_eq_coeff, SequenceCoefficients.r_difference, SequenceCoefficients.s_difference
two_E | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.r_difference_coeff
two_O | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.s_difference_coeff
coeff_pow_tuple | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.coeff_indicator
indicator_prod | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.coeff_indicator
coeff_indicator | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.coeff_E, SequenceCoefficients.coeff_O
coeff_E | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.r_difference_coeff
coeff_O | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.s_difference_coeff
T_functional | proof_shape: bind-only | frozen: T0,T2,T3 | escape_witness: none | consumers: SequenceCoefficients.H_functional, SequenceCoefficients.C_functional
U_functional | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.H_functional
H | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.H_functional, SequenceCoefficients.difference_series, SequenceCoefficients.r_difference_coeff, SequenceCoefficients.s_difference_coeff, SequenceCoefficients.h_eq_coeff, SequenceCoefficients.r_difference, SequenceCoefficients.s_difference
H_functional | proof_shape: bind-only | frozen: T0,T2,T3 | escape_witness: none | consumers: SequenceCoefficients.h_eq_coeff
C_functional | proof_shape: bind-only | frozen: T0,T2,T3 | escape_witness: none | consumers: SequenceCoefficients.c_eq_coeff
U_inverse | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.difference_series
difference_series | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.r_difference_coeff, SequenceCoefficients.s_difference_coeff
r_difference_coeff | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.r_difference
s_difference_coeff | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.s_difference
recur | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SixfoldMonotonicity.error_prefix, CoefficientTableChecker.tableCheck_sound, DyadicStatesLastThree.state_step_4, DyadicStatesLastThree.state_step_5, DyadicStatesLastThree.state_step_6, SequenceCoefficients.zrecur, SequenceCoefficients.recur_eq_coeff, SequenceCoefficients.errorTerm, SequenceCoefficients.r_difference, SequenceCoefficients.s_difference, DyadicPrefixBounds.tableH_sound, DyadicPrefixBounds.tableError_sound, DyadicPrefixBounds.h_seed, DyadicPrefixBounds.c_seed, DyadicPrefixBounds.h_prefix, DyadicPrefixBounds.c_prefix, DyadicPrefixBounds.seedH_exact, DyadicPrefixBounds.seedC_exact, DyadicPrefixBounds.h_dyadic, DyadicPrefixBounds.c_dyadic, DyadicStatesFirstThree.state, DyadicStatesFirstThree.recur_pos, DyadicStatesFirstThree.state_step_1, DyadicStatesFirstThree.state_step_2, DyadicStatesFirstThree.state_step_3, DyadicStatesFirstThree.stateZ_eq_state
zrecur | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.state_dyadic_bound, DyadicPrefixBounds.h_prefix, DyadicPrefixBounds.c_prefix, DyadicStatesFirstThree.stateZ
polyseries | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.polyseries_mul_coeff, SequenceCoefficients.recur_eq_coeff, SequenceCoefficients.p_H, SequenceCoefficients.p_C, SequenceCoefficients.h_eq_coeff, SequenceCoefficients.c_eq_coeff
polyseries_mul_coeff | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.recur_eq_coeff
recur_eq_coeff | proof_shape: content | frozen: none | escape_witness: recur_eq_coeff | consumers: SequenceCoefficients.h_eq_coeff, SequenceCoefficients.c_eq_coeff
p | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.h_matrix_bound, MatrixBounds.wordsCheck, MatrixBounds.c_five_bound, MatrixBounds.c_short_bound, MatrixBounds.c_word_bound, SixfoldMonotonicity.error_prefix, CoefficientTableChecker.table1_checked, CoefficientTableChecker.table1_sound, CoefficientTableChecker.table2_checked, CoefficientTableChecker.table2_sound, CoefficientTableChecker.table3_checked, CoefficientTableChecker.table3_sound, CoefficientTableChecker.table4_checked, CoefficientTableChecker.table4_sound, CoefficientTableChecker.table5_checked, CoefficientTableChecker.table5_sound, CoefficientTableChecker.table6_checked, CoefficientTableChecker.table6_sound, DyadicStatesLastThree.state_step_4, DyadicStatesLastThree.state_step_5, DyadicStatesLastThree.state_step_6, DyadicStatesLastThree.stateZ_step_4, DyadicStatesLastThree.stateZ_step_5, DyadicStatesLastThree.stateZ_step_6, SequenceCoefficients.p_H, SequenceCoefficients.p_C, SequenceCoefficients.h_eq_coeff, SequenceCoefficients.c_eq_coeff, SequenceCoefficients.errorTerm, SequenceCoefficients.r_difference, SequenceCoefficients.s_difference, DyadicPrefixBounds.tableH_sound, DyadicPrefixBounds.tableError_sound, DyadicPrefixBounds.h_step_norm, DyadicPrefixBounds.h_state_step, DyadicPrefixBounds.h_seed, DyadicPrefixBounds.c_seed, DyadicPrefixBounds.h_prefix, DyadicPrefixBounds.c_prefix, DyadicPrefixBounds.seedH_exact, DyadicPrefixBounds.seedC_exact, DyadicPrefixBounds.h_dyadic, DyadicPrefixBounds.c_dyadic, DyadicStatesFirstThree.state_step_1, DyadicStatesFirstThree.state_step_2, DyadicStatesFirstThree.state_step_3, DyadicStatesFirstThree.stateZ_step_1, DyadicStatesFirstThree.stateZ_step_2, DyadicStatesFirstThree.stateZ_step_3
p_H | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.h_eq_coeff
p_C | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.c_eq_coeff
h_eq_coeff | proof_shape: content | frozen: T0,T2,T3 | escape_witness: none | consumers: SequenceCoefficients.r_difference, SequenceCoefficients.s_difference
c_eq_coeff | proof_shape: content | frozen: T0,T2,T3 | escape_witness: none | consumers: SequenceCoefficients.r_difference, SequenceCoefficients.s_difference
errorTerm | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SixfoldMonotonicity.initial_r, SixfoldMonotonicity.initial_s, SixfoldMonotonicity.tail_positive, SixfoldMonotonicity.r_strict, SixfoldMonotonicity.s_strict, SequenceCoefficients.r_difference, SequenceCoefficients.s_difference, DyadicPrefixBounds.tableError_sound
r_difference | proof_shape: content | frozen: T0,T2,T3 | escape_witness: r_difference | consumers: SixfoldMonotonicity.initial_r, SixfoldMonotonicity.r_strict
s_difference | proof_shape: content | frozen: T0,T2,T3 | escape_witness: s_difference | consumers: SixfoldMonotonicity.initial_s, SixfoldMonotonicity.s_strict
Utility none: the declarations establish symbolic identities and recursions for arbitrary indices;
no standalone finite instance, numerical threshold reduction or certificate is asserted.
-/

import D5.S1.Words.Complexity.ThueMorseReducedAbelianOdd
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Expand

namespace D5.S1.Words.EvilOdious.SequenceCoefficients
noncomputable section

set_option autoImplicit false
open D5.S1.Words.Complexity

def r (j n : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple j n).filter
    (fun x => ∀ i, thueMorse (x i) = false)).card

def s (j n : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple j n).filter
    (fun x => ∀ i, thueMorse (x i) = true)).card



set_option autoImplicit false
open D5.S1.Words.Complexity Finset PowerSeries

private def E : PowerSeries ℤ := PowerSeries.mk (fun n => if thueMorse n then 0 else 1)
private def O : PowerSeries ℤ := PowerSeries.mk (fun n => if thueMorse n then 1 else 0)
private def T : PowerSeries ℤ := PowerSeries.mk (fun n => if thueMorse n then -1 else 1)

private theorem two_E : 2 * E = (PowerSeries.mk 1) + T := by
  ext n
  simp only [E, T, map_add, coeff_mk]
  rw [show (2 : PowerSeries ℤ) = C 2 by simp, coeff_C_mul]
  simp only [coeff_mk, Pi.one_apply]
  cases thueMorse n <;> norm_num

private theorem two_O : 2 * O = (PowerSeries.mk 1) - T := by
  ext n
  simp only [O, T, map_sub, coeff_mk]
  rw [show (2 : PowerSeries ℤ) = C 2 by simp, coeff_C_mul]
  simp only [coeff_mk, Pi.one_apply]
  cases thueMorse n <;> norm_num

private theorem coeff_pow_tuple (phi : PowerSeries ℤ) (j n : ℕ) :
    coeff n (phi ^ j) =
      ∑ x ∈ Finset.Nat.antidiagonalTuple j n, ∏ i, coeff (x i) phi := by
  have hp : (∏ _i : Fin j, phi) = phi ^ j := by simp
  rw [← hp, coeff_prod]
  apply Finset.sum_bij (fun (a : Fin j →₀ ℕ) _ => (fun i => a i))
  · intro a ha
    rw [Finset.Nat.mem_antidiagonalTuple]
    exact (Finset.mem_finsuppAntidiag.mp ha).1
  · intro a ha b hb hab
    exact Finsupp.ext (congrFun hab)
  · intro b hb
    let a : Fin j →₀ ℕ := Finsupp.equivFunOnFinite.symm b
    refine ⟨a, ?_, ?_⟩
    · simpa [a, Finset.mem_finsuppAntidiag] using Finset.Nat.mem_antidiagonalTuple.mp hb
    · exact Finsupp.equivFunOnFinite.apply_symm_apply b
  · intro a ha
    rfl

private theorem indicator_prod (b : Bool) (j : ℕ) (x : Fin j → ℕ) :
    (∏ i, (if thueMorse (x i) = b then (1 : ℤ) else 0)) =
      if (∀ i, thueMorse (x i) = b) then 1 else 0 := by
  classical
  have hh := (Fintype.prod_boole (p := fun i : Fin j => thueMorse (x i) = b) :
    (∏ i, (if thueMorse (x i) = b then (1 : ℤ) else 0)) = _)
  by_cases h : ∀ i, thueMorse (x i) = b
  · simpa only [if_pos h] using hh
  · simpa only [if_neg h] using hh

private theorem coeff_indicator (b : Bool) (j n : ℕ) :
    coeff n ((PowerSeries.mk (fun n => if thueMorse n = b then (1 : ℤ) else 0)) ^ j) =
      (((Finset.Nat.antidiagonalTuple j n).filter
        (fun x => ∀ i, thueMorse (x i) = b)).card : ℤ) := by
  classical
  rw [coeff_pow_tuple]
  simp only [coeff_mk, indicator_prod]
  simp

private theorem coeff_E (j n : ℕ) : coeff n (E ^ j) = (r j n : ℤ) := by
  have he : E = PowerSeries.mk (fun n => if thueMorse n = false then (1 : ℤ) else 0) := by
    ext k
    cases ht : thueMorse k <;> simp [E, ht]
  simpa only [← he, r] using coeff_indicator false j n

private theorem coeff_O (j n : ℕ) : coeff n (O ^ j) = (s j n : ℤ) := by
  have ho : O = PowerSeries.mk (fun n => if thueMorse n = true then (1 : ℤ) else 0) := by
    ext k
    cases ht : thueMorse k <;> simp [O, ht]
  simpa only [← ho, s] using coeff_indicator true j n




set_option autoImplicit false
open D5.S1.Words.Complexity Finset PowerSeries

private theorem T_functional : T = (1 - X) * (PowerSeries.expand 2 (by decide) T) := by
  ext n
  cases n with
  | zero => simp [T]
  | succ n =>
    simp only [sub_mul, one_mul, map_sub, coeff_succ_X_mul]
    rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
    · have hodd : ¬ 2 ∣ 2 * k + 1 := by omega
      simp [T, coeff_expand, hodd, thueMorse_two_mul_add_one]
      cases thueMorse k <;> norm_num
    · have heven : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      have hodd : ¬ 2 ∣ 2 * k + 1 := by omega
      simp [T, coeff_expand, heven, hodd, thueMorse_two_mul]

private theorem U_functional : (PowerSeries.mk 1 : PowerSeries ℤ) = (1 + X) * (PowerSeries.expand 2 (by decide) (PowerSeries.mk 1)) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [add_mul, one_mul, map_add, coeff_succ_X_mul]
    rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
    · have hodd : ¬ 2 ∣ 2 * k + 1 := by omega
      simp [coeff_expand, hodd]
    · have heven : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      have hodd : ¬ 2 ∣ 2 * k + 1 := by omega
      simp [coeff_expand, heven, hodd]

private def H (j : ℕ) : PowerSeries ℤ := T ^ j * (PowerSeries.mk 1) ^ (5 - j)

private theorem H_functional (j : ℕ) :
    H j = ((1 - X) ^ j * (1 + X) ^ (5 - j)) *
      PowerSeries.expand 2 (by decide) (H j) := by
  conv_lhs => rw [H, T_functional, U_functional]
  simp only [H, map_mul, map_pow, mul_pow]
  ring

private theorem C_functional :
    (T ^ 6) = (1 - X) ^ 6 * PowerSeries.expand 2 (by decide) (T ^ 6) := by
  conv_lhs => rw [ T_functional]
  simp only [ map_pow, mul_pow]




set_option autoImplicit false
open Finset PowerSeries


private theorem U_inverse : (1 - X) * (PowerSeries.mk 1) = (1 : PowerSeries ℤ) := by
  simpa [mul_comm] using mk_one_mul_one_sub_eq_one ℤ

private theorem difference_series (A : PowerSeries ℤ) (sigma : ℤ)
    (ha : 2 * A = (PowerSeries.mk 1) + C sigma * T) :
    C 64 * ((1 - X) * A ^ 6) =
      (PowerSeries.mk 1) ^ 5 + C (6 * sigma) * H 1 + C (15 * sigma ^ 2) * H 2 +
      C (20 * sigma ^ 3) * H 3 + C (15 * sigma ^ 4) * H 4 +
      C (6 * sigma ^ 5) * H 5 + C (sigma ^ 6) * ((1 - X) * (T ^ 6)) := by
  have hp : C 64 * A ^ 6 = ((PowerSeries.mk 1) + C sigma * T) ^ 6 := by
    calc
      C 64 * A ^ 6 = (2 * A) ^ 6 := by norm_num; ring
      _ = ((PowerSeries.mk 1) + C sigma * T) ^ 6 := congrArg (· ^ 6) ha
  have hpoly : (1 - X) * ((PowerSeries.mk 1) + C sigma * T) ^ 6 =
      ((1 - X) * (PowerSeries.mk 1)) *
        ((PowerSeries.mk 1) ^ 5 + 6 * C sigma * T * (PowerSeries.mk 1) ^ 4 + 15 * (C sigma) ^ 2 * T ^ 2 * (PowerSeries.mk 1) ^ 3 +
        20 * (C sigma) ^ 3 * T ^ 3 * (PowerSeries.mk 1) ^ 2 + 15 * (C sigma) ^ 4 * T ^ 4 * (PowerSeries.mk 1) +
        6 * (C sigma) ^ 5 * T ^ 5) + (C sigma) ^ 6 * ((1 - X) * T ^ 6) := by ring
  calc
    C 64 * ((1 - X) * A ^ 6) = (1 - X) * (C 64 * A ^ 6) := by ring
    _ = (1 - X) * ((PowerSeries.mk 1) + C sigma * T) ^ 6 := by rw [hp]
    _ = _ := by
      rw [hpoly, U_inverse]
      simp only [H, Nat.reduceSub, map_mul, map_pow, one_mul]
      norm_num
      ring

private theorem r_difference_coeff (n : ℕ) :
    64 * ((r 6 (n + 1) : ℤ) - r 6 n) =
      ((n + 5).choose 4 : ℤ) + 6 * (PowerSeries.coeff (n + 1) (H 1)) + 15 * (PowerSeries.coeff (n + 1) (H 2)) +
      20 * (PowerSeries.coeff (n + 1) (H 3)) + 15 * (PowerSeries.coeff (n + 1) (H 4)) + 6 * (PowerSeries.coeff (n + 1) (H 5)) +
      (PowerSeries.coeff (n + 1) (T ^ 6)) - (PowerSeries.coeff n (T ^ 6)) := by
  have hh := congrArg (coeff (n + 1)) (difference_series E 1 (by simpa using two_E))
  have hu : coeff (n + 1) ((PowerSeries.mk 1) ^ 5) = ((n + 5).choose 4 : ℤ) := by
    rw [mk_one_pow_eq_mk_choose_add ℤ 4, coeff_mk]
    congr 2
    omega
  norm_num only [map_mul, map_pow, map_one, one_mul, mul_one, Int.reduceMul, Int.reducePow] at hh
  simp only [map_add, coeff_C_mul, sub_mul, one_mul, map_sub, coeff_succ_X_mul, coeff_E, hu] at hh
  simpa only [ add_sub_assoc] using hh

private theorem s_difference_coeff (n : ℕ) :
    64 * ((s 6 (n + 1) : ℤ) - s 6 n) =
      ((n + 5).choose 4 : ℤ) - 6 * (PowerSeries.coeff (n + 1) (H 1)) + 15 * (PowerSeries.coeff (n + 1) (H 2)) -
      20 * (PowerSeries.coeff (n + 1) (H 3)) + 15 * (PowerSeries.coeff (n + 1) (H 4)) - 6 * (PowerSeries.coeff (n + 1) (H 5)) +
      (PowerSeries.coeff (n + 1) (T ^ 6)) - (PowerSeries.coeff n (T ^ 6)) := by
  have hh := congrArg (coeff (n + 1)) (difference_series O (-1) (by simpa [sub_eq_add_neg] using two_O))
  have hu : coeff (n + 1) ((PowerSeries.mk 1) ^ 5) = ((n + 5).choose 4 : ℤ) := by
    rw [mk_one_pow_eq_mk_choose_add ℤ 4, coeff_mk]
    congr 2
    omega
  norm_num only [map_mul, map_pow, map_one, one_mul, mul_one, Int.reduceMul, Int.reducePow] at hh
  simp only [map_add, coeff_C_mul, sub_mul, one_mul, map_sub, coeff_succ_X_mul, coeff_O, hu] at hh
  linear_combination hh




set_option autoImplicit false
open Finset PowerSeries


def recur (p : List ℤ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => ∑ k ∈ Finset.range p.length,
      if k ≤ n + 1 ∧ 2 ∣ n + 1 - k then (List.getD p k 0) * recur p ((n + 1 - k) / 2) else 0
termination_by n => n
decreasing_by all_goals omega

def zrecur (p : List ℤ) (n : ℤ) : ℤ := if 0 ≤ n then recur p n.toNat else 0

private noncomputable def polyseries (p : List ℤ) : PowerSeries ℤ :=
  ∑ k ∈ Finset.range p.length, C ((List.getD p k 0)) * X ^ k

private theorem polyseries_mul_coeff (p : List ℤ) (F : PowerSeries ℤ) (n : ℕ) :
    coeff n (polyseries p * PowerSeries.expand 2 (by decide) F) =
      ∑ k ∈ Finset.range p.length,
        if k ≤ n ∧ 2 ∣ n - k then (List.getD p k 0) * coeff ((n - k) / 2) F else 0 := by
  classical
  simp only [polyseries, sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_expand]
  split_ifs <;> simp_all

private theorem recur_eq_coeff (p : List ℤ) (F : PowerSeries ℤ)
    (hzero : coeff 0 F = 1)
    (hfunc : F = polyseries p * PowerSeries.expand 2 (by decide) F) :
    ∀ n, recur p n = coeff n F := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [recur] using hzero.symm
    | succ n =>
      conv_rhs => rw [hfunc, polyseries_mul_coeff]
      rw [recur]
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs with h
      · rw [ih _ (by omega)]
      · rfl




set_option autoImplicit false
open Finset PowerSeries

def p (j : ℕ) : List ℤ :=
  match j with
  | 1 => [1, 3, 2, -2, -3, -1]
  | 2 => [1, 1, -2, -2, 1, 1]
  | 3 => [1, -1, -2, 2, 1, -1]
  | 4 => [1, -3, 2, 2, -3, 1]
  | 5 => [1, -5, 10, -10, 5, -1]
  | _ => [1, -6, 15, -20, 15, -6, 1]


private theorem p_H (j : ℕ) (hj : j ∈ Finset.Icc 1 5) :
    polyseries (p j) = (1 - X) ^ j * (1 + X) ^ (5 - j) := by
  rcases Finset.mem_Icc.mp hj with ⟨hl, hu⟩
  interval_cases j <;>
    simp [p, polyseries, List.getD, Finset.sum_range_succ] <;> ring

private theorem p_C : polyseries (p 6) = (1 - X : PowerSeries ℤ) ^ 6 := by
  simp [p, polyseries, List.getD, Finset.sum_range_succ]
  ring

private theorem h_eq_coeff (j n : ℕ) (hj : j ∈ Finset.Icc 1 5) : (recur (p j) n) = (PowerSeries.coeff n (H j)) := by
  apply recur_eq_coeff (p j) (H j) _ _ n
  · simp [H, T, coeff_zero_eq_constantCoeff]
  · rw [p_H j hj]
    exact H_functional j

private theorem c_eq_coeff (n : ℕ) : (recur (p 6) n) = (PowerSeries.coeff n (T ^ 6)) := by
  apply recur_eq_coeff (p 6) (T ^ 6) _ _ n
  · simp [ T, coeff_zero_eq_constantCoeff]
  · rw [p_C]
    exact C_functional




set_option autoImplicit false
open Finset

def errorTerm (sigma : ℤ) (n : ℕ) : ℤ :=
  (∑ j ∈ Finset.Icc 1 5, sigma ^ j * (Nat.choose 6 j : ℤ) * (recur (p j) n)) + (recur (p 6) n) - (recur (p 6) (n - 1))

theorem r_difference (n : ℕ) (hn : 1 ≤ n) :
    64 * ((r 6 n : ℤ) - r 6 (n - 1)) = ((n + 4).choose 4 : ℤ) + errorTerm 1 n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hh := r_difference_coeff m
  rw [← h_eq_coeff 1 (m+1) (by decide), ← h_eq_coeff 2 (m+1) (by decide),
    ← h_eq_coeff 3 (m+1) (by decide), ← h_eq_coeff 4 (m+1) (by decide),
    ← h_eq_coeff 5 (m+1) (by decide), ← c_eq_coeff (m+1), ← c_eq_coeff m] at hh
  have hI : Finset.Icc 1 5 = {1,2,3,4,5} := by decide
  have h2 : Nat.choose 6 2 = 15 := by decide
  have h3 : Nat.choose 6 3 = 20 := by decide
  have h4 : Nat.choose 6 4 = 15 := by decide
  norm_num [errorTerm, hI, h2, h3, h4]
  linear_combination hh

theorem s_difference (n : ℕ) (hn : 1 ≤ n) :
    64 * ((s 6 n : ℤ) - s 6 (n - 1)) = ((n + 4).choose 4 : ℤ) + errorTerm (-1) n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hh := s_difference_coeff m
  rw [← h_eq_coeff 1 (m+1) (by decide), ← h_eq_coeff 2 (m+1) (by decide),
    ← h_eq_coeff 3 (m+1) (by decide), ← h_eq_coeff 4 (m+1) (by decide),
    ← h_eq_coeff 5 (m+1) (by decide), ← c_eq_coeff (m+1), ← c_eq_coeff m] at hh
  have hI : Finset.Icc 1 5 = {1,2,3,4,5} := by decide
  have h2 : Nat.choose 6 2 = 15 := by decide
  have h3 : Nat.choose 6 3 = 20 := by decide
  have h4 : Nat.choose 6 4 = 15 := by decide
  norm_num [errorTerm, hI, h2, h3, h4]
  linear_combination hh

end
end D5.S1.Words.EvilOdious.SequenceCoefficients
