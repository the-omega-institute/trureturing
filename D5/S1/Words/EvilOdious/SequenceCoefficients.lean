/- GID: D5/S1/Words/EvilOdious/SequenceCoefficients
   generality: I
   mirror-B: D5/B/S1/Words/EvilOdious/SequenceCoefficients
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S1/Words/EvilOdious/SixfoldMonotonicity.tail_positive; premises=D5/S1/Words/EvilOdious/SequenceCoefficients.h_matrix_bound,D5/S1/Words/EvilOdious/SequenceCoefficients.c_five_checked,D5/S1/Words/EvilOdious/SequenceCoefficients.c_short_checked
   digest: Sixfold Thue-Morse counts are controlled by dyadic coefficient states. -/
/-
admission_basis: escape-witness
Module escape_witness: r_difference
Direct frozen dependencies: aliases below denote declaration identities, not module pins.
T0 = D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.thueMorse
  statement_id: sha256:64e3518f7565865a40ea42fed02d3ec99a43a5957584903476dff7ab488bd8b0
T1 = D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.thueMorse_two_mul
  statement_id: sha256:bf55640ac023e7929642cb19d30dba7694cf92e3200ef026c879f77a1293cbca
T2 = D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.thueMorse_two_mul_add_one
  statement_id: sha256:d2a4385c4493b662cbf5172983c049e669dd2404058476ba99c3a7b487ac5009
T3 = D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.thueMorse_zero
  statement_id: sha256:830774b316987f051dd08fe872da1db8a384c01f25bfe4b814f009c8573cb6b2
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15228.
Declaration rows: name | proof_shape | frozen dependencies | escape_witness | consumers.
Definitions carry bind-only as an organization label; no proof content is claimed for them.
r | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.coeff_E, SequenceCoefficients.r_difference, SequenceCoefficients.r_difference_coeff, SixfoldMonotonicity.claim, SixfoldMonotonicity.initial_r, SixfoldMonotonicity.r_strict, SixfoldMonotonicity.result
s | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.coeff_O, SequenceCoefficients.s_difference, SequenceCoefficients.s_difference_coeff, SixfoldMonotonicity.claim, SixfoldMonotonicity.initial_s, SixfoldMonotonicity.result, SixfoldMonotonicity.s_strict
E | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.coeff_E, SequenceCoefficients.r_difference_coeff, SequenceCoefficients.two_E
O | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.coeff_O, SequenceCoefficients.s_difference_coeff, SequenceCoefficients.two_O
T | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.C_functional, SequenceCoefficients.H, SequenceCoefficients.H_functional, SequenceCoefficients.T_functional, SequenceCoefficients.c_eq_coeff, SequenceCoefficients.difference_series, SequenceCoefficients.h_eq_coeff, SequenceCoefficients.r_difference, SequenceCoefficients.r_difference_coeff, SequenceCoefficients.s_difference, SequenceCoefficients.s_difference_coeff, SequenceCoefficients.two_E, SequenceCoefficients.two_O
two_E | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.r_difference_coeff
two_O | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.s_difference_coeff
coeff_pow_tuple | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.coeff_indicator
indicator_prod | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.coeff_indicator
coeff_indicator | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.coeff_E, SequenceCoefficients.coeff_O
coeff_E | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.r_difference_coeff
coeff_O | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.s_difference_coeff
T_functional | proof_shape: bind-only | frozen: T0,T1,T2 | escape_witness: none | consumers: SequenceCoefficients.C_functional, SequenceCoefficients.H_functional
U_functional | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.H_functional
H | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.H_functional, SequenceCoefficients.difference_series, SequenceCoefficients.h_eq_coeff, SequenceCoefficients.r_difference, SequenceCoefficients.r_difference_coeff, SequenceCoefficients.s_difference, SequenceCoefficients.s_difference_coeff
H_functional | proof_shape: bind-only | frozen: T0,T1,T2 | escape_witness: none | consumers: SequenceCoefficients.h_eq_coeff
C_functional | proof_shape: bind-only | frozen: T0,T1,T2 | escape_witness: none | consumers: SequenceCoefficients.c_eq_coeff
U_inverse | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.difference_series
difference_series | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.r_difference_coeff, SequenceCoefficients.s_difference_coeff
r_difference_coeff | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.r_difference
s_difference_coeff | proof_shape: bind-only | frozen: T0 | escape_witness: none | consumers: SequenceCoefficients.s_difference
recur | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.c_dyadic, CoefficientTableChecker.c_prefix, CoefficientTableChecker.h_dyadic, CoefficientTableChecker.seedC_exact, CoefficientTableChecker.seedH_exact, CoefficientTableChecker.tableCheck_sound, CoefficientTableChecker.tableError_sound, CoefficientTableChecker.tableH_sound, SequenceCoefficients.errorTerm, SequenceCoefficients.r_difference, SequenceCoefficients.recur_eq_coeff, SequenceCoefficients.recur_pos, SequenceCoefficients.s_difference, SequenceCoefficients.state, SequenceCoefficients.stateZ_eq_state, SequenceCoefficients.state_step_dim5, SequenceCoefficients.state_step_dim6, SequenceCoefficients.zrecur, SixfoldMonotonicity.error_prefix
zrecur | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.c_dyadic, CoefficientTableChecker.h_dyadic, SequenceCoefficients.stateZ, SequenceCoefficients.state_dyadic_bound
polyseries | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.c_eq_coeff, SequenceCoefficients.h_eq_coeff, SequenceCoefficients.p_C, SequenceCoefficients.p_H, SequenceCoefficients.polyseries_mul_coeff, SequenceCoefficients.recur_eq_coeff
polyseries_mul_coeff | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.recur_eq_coeff
recur_eq_coeff | proof_shape: content | frozen: none | escape_witness: D5.S1.Words.EvilOdious.SequenceCoefficients.recur_eq_coeff | consumers: SequenceCoefficients.c_eq_coeff, SequenceCoefficients.h_eq_coeff
p | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.c_dyadic, CoefficientTableChecker.c_prefix, CoefficientTableChecker.h_dyadic, CoefficientTableChecker.h_state_step, CoefficientTableChecker.h_step_norm, CoefficientTableChecker.seedC_exact, CoefficientTableChecker.seedH_exact, CoefficientTableChecker.table1_checked, CoefficientTableChecker.table1_sound, CoefficientTableChecker.table2_checked, CoefficientTableChecker.table2_sound, CoefficientTableChecker.table3_checked, CoefficientTableChecker.table3_sound, CoefficientTableChecker.table4_checked, CoefficientTableChecker.table4_sound, CoefficientTableChecker.table5_checked, CoefficientTableChecker.table5_sound, CoefficientTableChecker.table6_checked, CoefficientTableChecker.table6_sound, CoefficientTableChecker.tableError_sound, CoefficientTableChecker.tableH_sound, SequenceCoefficients.c_eq_coeff, SequenceCoefficients.c_five_bound, SequenceCoefficients.c_short_bound, SequenceCoefficients.c_word_bound, SequenceCoefficients.errorTerm, SequenceCoefficients.h_eq_coeff, SequenceCoefficients.h_matrix_bound, SequenceCoefficients.p_C, SequenceCoefficients.p_H, SequenceCoefficients.r_difference, SequenceCoefficients.s_difference, SequenceCoefficients.stateZ_step_1, SequenceCoefficients.stateZ_step_2, SequenceCoefficients.stateZ_step_3, SequenceCoefficients.stateZ_step_4, SequenceCoefficients.stateZ_step_5, SequenceCoefficients.stateZ_step_6, SequenceCoefficients.state_step_1, SequenceCoefficients.state_step_2, SequenceCoefficients.state_step_3, SequenceCoefficients.state_step_4, SequenceCoefficients.state_step_5, SequenceCoefficients.state_step_6, SequenceCoefficients.wordsCheck, SixfoldMonotonicity.error_prefix
p_H | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.h_eq_coeff
p_C | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.c_eq_coeff
h_eq_coeff | proof_shape: content | frozen: T0,T3,T1,T2 | escape_witness: D5.S1.Words.EvilOdious.SequenceCoefficients.recur_eq_coeff | consumers: SequenceCoefficients.r_difference, SequenceCoefficients.s_difference
c_eq_coeff | proof_shape: content | frozen: T0,T3,T1,T2 | escape_witness: D5.S1.Words.EvilOdious.SequenceCoefficients.recur_eq_coeff | consumers: SequenceCoefficients.r_difference, SequenceCoefficients.s_difference
errorTerm | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.tableError_sound, SequenceCoefficients.r_difference, SequenceCoefficients.s_difference, SixfoldMonotonicity.initial_r, SixfoldMonotonicity.initial_s, SixfoldMonotonicity.r_strict, SixfoldMonotonicity.s_strict, SixfoldMonotonicity.tail_positive
r_difference | proof_shape: content | frozen: T0,T3,T1,T2 | escape_witness: D5.S1.Words.EvilOdious.SequenceCoefficients.recur_eq_coeff | consumers: SixfoldMonotonicity.initial_r, SixfoldMonotonicity.r_strict
s_difference | proof_shape: content | frozen: T0,T3,T1,T2 | escape_witness: D5.S1.Words.EvilOdious.SequenceCoefficients.recur_eq_coeff | consumers: SixfoldMonotonicity.initial_s, SixfoldMonotonicity.s_strict
matrixBound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.h_dyadic, CoefficientTableChecker.h_step_norm, CoefficientTableChecker.word_bound_of_step, SequenceCoefficients.c_five_bound, SequenceCoefficients.c_short_bound, SequenceCoefficients.c_word_bound, SequenceCoefficients.h_matrix_bound, SequenceCoefficients.matrix_apply_bound, SequenceCoefficients.state_dyadic_bound, SequenceCoefficients.vector_prefix_bound, SequenceCoefficients.wordsCheck
vectorBound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.matrix_apply_bound, SequenceCoefficients.state_dyadic_bound, SequenceCoefficients.vector_prefix_bound
matrixBound_iff_norm | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.c_word_bound, SequenceCoefficients.matrix_apply_bound
vectorBound_iff_norm | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.matrix_apply_bound
matrix_apply_bound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.vector_prefix_bound
pz | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.stateMatrix
stateMatrix | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.c_dyadic, CoefficientTableChecker.h_dyadic, CoefficientTableChecker.h_state_step, CoefficientTableChecker.h_step_norm, SequenceCoefficients.c_five_bound, SequenceCoefficients.c_short_bound, SequenceCoefficients.c_word_bound, SequenceCoefficients.h_matrix_bound, SequenceCoefficients.stateZ_step_1, SequenceCoefficients.stateZ_step_2, SequenceCoefficients.stateZ_step_3, SequenceCoefficients.stateZ_step_4, SequenceCoefficients.stateZ_step_5, SequenceCoefficients.stateZ_step_6, SequenceCoefficients.state_step_1, SequenceCoefficients.state_step_2, SequenceCoefficients.state_step_3, SequenceCoefficients.state_step_4, SequenceCoefficients.state_step_5, SequenceCoefficients.state_step_6, SequenceCoefficients.state_step_dim5, SequenceCoefficients.state_step_dim6, SequenceCoefficients.wordsCheck
words | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.c_five_bound, SequenceCoefficients.c_short_bound, SequenceCoefficients.wordsCheck
mem_words | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.c_five_bound, SequenceCoefficients.c_short_bound
wordMatrix | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.h_dyadic, CoefficientTableChecker.word_bound_of_step, SequenceCoefficients.c_five_bound, SequenceCoefficients.c_short_bound, SequenceCoefficients.c_word_bound, SequenceCoefficients.state_dyadic_bound, SequenceCoefficients.state_word, SequenceCoefficients.vector_prefix_bound, SequenceCoefficients.wordsCheck
instDecidableMatrixBound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.c_five_bound, SequenceCoefficients.c_short_bound, SequenceCoefficients.h_matrix_bound, SequenceCoefficients.wordsCheck
h_matrix_bound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.h_step_norm
wordsCheck | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.c_five_checked, SequenceCoefficients.c_short_bound, SequenceCoefficients.c_short_checked
c_five_checked | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.c_five_bound
c_short_checked | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.c_short_bound
c_five_bound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.c_word_bound
c_short_bound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.c_word_bound
c_word_bound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.c_dyadic
state | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.stateZ_eq_state, SequenceCoefficients.stateZ_step_1, SequenceCoefficients.stateZ_step_2, SequenceCoefficients.stateZ_step_3, SequenceCoefficients.stateZ_step_4, SequenceCoefficients.stateZ_step_5, SequenceCoefficients.stateZ_step_6, SequenceCoefficients.state_step_1, SequenceCoefficients.state_step_2, SequenceCoefficients.state_step_3, SequenceCoefficients.state_step_4, SequenceCoefficients.state_step_5, SequenceCoefficients.state_step_6, SequenceCoefficients.state_step_dim5, SequenceCoefficients.state_step_dim6
recur_pos | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.state_step_dim5, SequenceCoefficients.state_step_dim6
state_step_dim5 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.state_step_1, SequenceCoefficients.state_step_2, SequenceCoefficients.state_step_3, SequenceCoefficients.state_step_4, SequenceCoefficients.state_step_5
state_step_dim6 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.state_step_6
state_step_1 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.stateZ_step_1
state_step_2 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.stateZ_step_2
state_step_3 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.stateZ_step_3
stateZ | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.c_dyadic, CoefficientTableChecker.h_dyadic, CoefficientTableChecker.h_state_step, SequenceCoefficients.stateZ_eq_state, SequenceCoefficients.stateZ_step_1, SequenceCoefficients.stateZ_step_2, SequenceCoefficients.stateZ_step_3, SequenceCoefficients.stateZ_step_4, SequenceCoefficients.stateZ_step_5, SequenceCoefficients.stateZ_step_6, SequenceCoefficients.state_dyadic_bound, SequenceCoefficients.state_word, SequenceCoefficients.vector_prefix_bound
stateZ_eq_state | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.stateZ_step_1, SequenceCoefficients.stateZ_step_2, SequenceCoefficients.stateZ_step_3, SequenceCoefficients.stateZ_step_4, SequenceCoefficients.stateZ_step_5, SequenceCoefficients.stateZ_step_6
stateZ_step_1 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.h_state_step
stateZ_step_2 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.h_state_step
stateZ_step_3 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.h_state_step
appendValue | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.c_prefix, SequenceCoefficients.appendValue_decompose, SequenceCoefficients.lowWord_bound, SequenceCoefficients.state_dyadic_bound, SequenceCoefficients.state_word, SequenceCoefficients.vector_prefix_bound, SequenceCoefficients.word_for_low, SixfoldMonotonicity.error_prefix, SixfoldMonotonicity.prefix_exists, SixfoldMonotonicity.prefix_scale_lower, SixfoldMonotonicity.tail_positive
state_word | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.vector_prefix_bound
vector_prefix_bound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.state_dyadic_bound
state_step_4 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.stateZ_step_4
state_step_5 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.stateZ_step_5
state_step_6 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.stateZ_step_6
stateZ_step_4 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.h_state_step
stateZ_step_5 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.h_state_step
stateZ_step_6 | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.c_dyadic
appendValue_decompose | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.c_prefix, SequenceCoefficients.state_dyadic_bound, SixfoldMonotonicity.error_prefix, SixfoldMonotonicity.prefix_exists, SixfoldMonotonicity.prefix_scale_lower
lowWord_bound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.c_prefix, SixfoldMonotonicity.error_prefix
word_for_low | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: SequenceCoefficients.state_dyadic_bound, SixfoldMonotonicity.prefix_exists
state_dyadic_bound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: CoefficientTableChecker.c_dyadic, CoefficientTableChecker.h_dyadic
Content reason: recur_eq_coeff identifies arbitrary recursively computed coefficients by strong induction.
r_difference uses this recurrence uniqueness on its live coefficient reconstruction path.
-/
import D5.S1.Words.Complexity.ThueMorseReducedAbelianOdd
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.List.Sections
import Mathlib.Data.List.SplitLengths
namespace D5.S1.Words.EvilOdious.SequenceCoefficients
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable section
open D5.S1.Words.Complexity
def r (j n : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple j n).filter
    (fun x => ∀ i, thueMorse (x i) = false)).card
def s (j n : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple j n).filter
    (fun x => ∀ i, thueMorse (x i) = true)).card
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
  · have ht : constantCoeff T = (1 : ℤ) := by
      change (if thueMorse 0 then (-1 : ℤ) else 1) = 1
      rw [thueMorse_zero]
      rfl
    simp [H, coeff_zero_eq_constantCoeff, ht]
  · rw [p_H j hj]
    exact H_functional j
private theorem c_eq_coeff (n : ℕ) : (recur (p 6) n) = (PowerSeries.coeff n (T ^ 6)) := by
  apply recur_eq_coeff (p 6) (T ^ 6) _ _ n
  · have ht : constantCoeff T = (1 : ℤ) := by
      change (if thueMorse 0 then (-1 : ℤ) else 1) = 1
      rw [thueMorse_zero]
      rfl
    simp [coeff_zero_eq_constantCoeff, ht]
  · rw [p_C]
    exact C_functional
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
open Finset Matrix
def matrixBound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (B : ℕ) : Prop :=
  ∀ i, ∑ j, (A i j).natAbs ≤ B
def vectorBound {d : ℕ} (v : Fin d → ℤ) (B : ℕ) : Prop :=
  ∀ i, (v i).natAbs ≤ B
open scoped Matrix.Norms.Operator
private theorem matrixBound_iff_norm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (B : ℕ) :
    matrixBound A B ↔ ‖A‖₊ ≤ (B : NNReal) := by
  simp only [matrixBound, Matrix.linfty_opNNNorm_def, Finset.sup_le_iff,
    Finset.mem_univ, forall_true_left, ← NNReal.natCast_natAbs, ← Nat.cast_sum, Nat.cast_le]
private theorem vectorBound_iff_norm {d : ℕ} (v : Fin d → ℤ) (B : ℕ) :
    vectorBound v B ↔ ‖v‖₊ ≤ (B : NNReal) := by
  simp only [vectorBound, pi_nnnorm_le_iff, ← NNReal.natCast_natAbs, Nat.cast_le]
theorem matrix_apply_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (v : Fin d → ℤ) (B K : ℕ) (ha : matrixBound A B) (hv : vectorBound v K) :
    vectorBound (A.mulVec v) (B * K) := by
  apply (vectorBound_iff_norm _ _).mpr
  simpa only [Nat.cast_mul] using
    (Matrix.linfty_opNNNorm_mulVec A v).trans (mul_le_mul' ((matrixBound_iff_norm _ _).mp ha) ((vectorBound_iff_norm _ _).mp hv))

def pz (p : List ℤ) (k : ℤ) : ℤ := if 0 ≤ k then (List.getD p k.toNat 0) else 0
def stateMatrix (d : ℕ) (p : List ℤ) (b : Bool) : Matrix (Fin d) (Fin d) ℤ :=
  fun i a => pz p (2 * (a : ℤ) + (if b then 1 else 0) - i)
def words (n : ℕ) : List (List Bool) := (List.replicate n [false, true]).sections
private theorem mem_words (w : List Bool) : w ∈ words w.length := by
  apply List.mem_sections.mpr
  apply List.forall₂_of_length_eq_of_get (by simp)
  intro i h₁ h₂
  simp only [List.get_eq_getElem, List.getElem_replicate]
  cases w[i] <;> simp
def wordMatrix {d : ℕ} (M : Bool → Matrix (Fin d) (Fin d) ℤ)
    (w : List Bool) : Matrix (Fin d) (Fin d) ℤ := (w.map M).prod

private instance instDecidableMatrixBound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (B : ℕ) : Decidable (matrixBound A B) :=
  inferInstanceAs (Decidable (∀ i : Fin d, ∑ j, (A i j).natAbs ≤ B))
theorem h_matrix_bound :
    matrixBound (stateMatrix 5 (p 1) false) 6 ∧ matrixBound (stateMatrix 5 (p 1) true) 6 ∧
    matrixBound (stateMatrix 5 (p 2) false) 4 ∧ matrixBound (stateMatrix 5 (p 2) true) 4 ∧
    matrixBound (stateMatrix 5 (p 3) false) 4 ∧ matrixBound (stateMatrix 5 (p 3) true) 4 ∧
    matrixBound (stateMatrix 5 (p 4) false) 6 ∧ matrixBound (stateMatrix 5 (p 4) true) 6 ∧
    matrixBound (stateMatrix 5 (p 5) false) 16 ∧ matrixBound (stateMatrix 5 (p 5) true) 16 := by
  decide +kernel
def wordsCheck (len bound : ℕ) : Bool :=
  (words len).all (fun w => decide (matrixBound (wordMatrix (stateMatrix 6 (p 6)) w) bound))
theorem c_five_checked : wordsCheck 5 1019200 = true := by decide +kernel
private theorem c_short_checked :
    (List.range 5).all (fun len => wordsCheck len (2 * 16 ^ len)) = true := by decide +kernel
private theorem c_five_bound (w : List Bool) (hw : w.length = 5) :
    matrixBound (wordMatrix (stateMatrix 6 (p 6)) w) (16 ^ 5) := by
  have h := List.all_eq_true.mp c_five_checked w (by rw [← hw]; exact mem_words w)
  have hb : matrixBound (wordMatrix (stateMatrix 6 (p 6)) w) 1019200 := of_decide_eq_true h
  intro i
  exact (hb i).trans (by decide)
private theorem c_short_bound (w : List Bool) (hw : w.length < 5) :
    matrixBound (wordMatrix (stateMatrix 6 (p 6)) w) (2 * 16 ^ w.length) := by
  have h := List.all_eq_true.mp c_short_checked w.length (List.mem_range.mpr hw)
  exact of_decide_eq_true (List.all_eq_true.mp h w (mem_words w))
theorem c_word_bound (w : List Bool) : matrixBound (wordMatrix (stateMatrix 6 (p 6)) w) (2 * 16 ^ w.length) := by
  letI := Matrix.linftyOpSemiNormedRing (n := Fin 6) (α := ℤ)
  let k := w.length / 5
  let v := w.take (5*k)
  let tail := w.drop (5*k)
  have hk : 5*k ≤ w.length := by dsimp [k]; omega
  have hv : v.length = 5*k := by simp [v, List.length_take, Nat.min_eq_left hk]
  have ht : tail.length = w.length % 5 := by simp [tail, k]; omega
  let sizes := List.replicate k 5
  let blocks := sizes.splitLengths v
  have hsz : sizes.sum = v.length := by simp [sizes, hv, Nat.mul_comm]
  have hflat : blocks.flatten = v := List.flatten_splitLengths v sizes (by omega)
  have hlengths : blocks.map List.length = sizes := List.map_splitLengths_length v sizes (by omega)
  have hblen : blocks.length = k := by simp [blocks, sizes]
  have hblock (x : List Bool) (hx : x ∈ blocks) :
      ‖wordMatrix (stateMatrix 6 (p 6)) x‖₊ ≤ ((16 ^ 5 : ℕ) : NNReal) := by
    have hmem : x.length ∈ blocks.map List.length := List.mem_map.mpr ⟨x,hx,rfl⟩
    rw [hlengths] at hmem
    have hxlen : x.length = 5 := (List.mem_replicate.mp hmem).2
    exact (matrixBound_iff_norm _ _).mp (c_five_bound x hxlen)
  have hprod := List.nnnorm_prod_le (blocks.map (wordMatrix (stateMatrix 6 (p 6))))
  have hpow := List.prod_le_pow_card
    ((blocks.map (wordMatrix (stateMatrix 6 (p 6)))).map nnnorm)
    (((16 ^ 5 : ℕ) : NNReal)) (by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      exact hblock b hb)
  have heq : wordMatrix (stateMatrix 6 (p 6)) v =
      (blocks.map (wordMatrix (stateMatrix 6 (p 6)))).prod := by
    rw [← hflat]
    simp only [wordMatrix, List.map_flatten, List.prod_flatten, List.map_map, Function.comp_def]
    rfl
  have hvnorm : ‖wordMatrix (stateMatrix 6 (p 6)) v‖₊ ≤
      (((16 ^ 5 : ℕ) : NNReal)) ^ k := by
    rw [heq]
    simpa only [List.length_map, hblen] using hprod.trans hpow
  have htail := (matrixBound_iff_norm _ _).mp (c_short_bound tail (by rw [ht]; omega))
  apply (matrixBound_iff_norm _ _).mpr
  have happ : wordMatrix (stateMatrix 6 (p 6)) w =
      wordMatrix (stateMatrix 6 (p 6)) v * wordMatrix (stateMatrix 6 (p 6)) tail := by
    simp only [wordMatrix, v, tail, ← List.prod_append, ← List.map_append, List.take_append_drop]
  have bound := (Matrix.linfty_opNNNorm_mul
    (wordMatrix (stateMatrix 6 (p 6)) v) (wordMatrix (stateMatrix 6 (p 6)) tail)).trans
    (mul_le_mul' hvnorm htail)
  rw [← happ] at bound
  have e : 5*k + w.length%5 = w.length := by dsimp [k]; omega
  have scalar : (((16 ^ 5 : ℕ) : NNReal)) ^ k * ((2 * 16 ^ tail.length : ℕ) : NNReal) =
      ((2 * 16 ^ w.length : ℕ) : NNReal) := by
    rw [ht]
    have scalarNat : (16 ^ 5) ^ k * (2 * 16 ^ (w.length % 5)) = 2 * 16 ^ w.length := by
      calc
        (16 ^ 5) ^ k * (2 * 16 ^ (w.length % 5)) =
            16 ^ (5*k) * (2 * 16 ^ (w.length % 5)) := by rw [pow_mul]
        _ = 2 * 16 ^ w.length := by rw [mul_left_comm, ← pow_add, e]
    exact_mod_cast scalarNat
  simpa only [scalar] using bound
def state (d : ℕ) (q : List ℤ) (n : ℕ) : Fin d → ℤ := fun i => recur q (n - i)
theorem recur_pos (q : List ℤ) (N : ℕ) (hn : 0 < N) :
    recur q N = ∑ k ∈ Finset.range q.length,
      if k ≤ N ∧ 2 ∣ N - k then (List.getD q k 0) * recur q ((N - k) / 2) else 0 := by
  cases N with
  | zero => omega
  | succ n => rw [recur]
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Finset Matrix
private theorem state_step_dim5 (a0 a1 a2 a3 a4 a5 : ℤ) (n : ℕ) (hn : 6 ≤ n) (b : Bool) :
    state 5 [a0, a1, a2, a3, a4, a5] (2 * n + (if b then 1 else 0)) =
      (stateMatrix 5 [a0, a1, a2, a3, a4, a5] b).mulVec (state 5 [a0, a1, a2, a3, a4, a5] n) := by
  ext i
  fin_cases i <;> cases b
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n := (by omega); have hd0 : 2 ∣ (2 * n) := (by omega); have hq0 : ((2 * n)) / 2 = n - 0 := by omega
    have hl1 : 1 ≤ 2 * n := (by omega); have hd1 : ¬ 2 ∣ (2 * n) - 1 := by omega
    have hl2 : 2 ≤ 2 * n := (by omega); have hd2 : 2 ∣ (2 * n) - 2 := (by omega); have hq2 : ((2 * n) - 2) / 2 = n - 1 := by omega
    have hl3 : 3 ≤ 2 * n := (by omega); have hd3 : ¬ 2 ∣ (2 * n) - 3 := by omega
    have hl4 : 4 ≤ 2 * n := (by omega); have hd4 : 2 ∣ (2 * n) - 4 := (by omega); have hq4 : ((2 * n) - 4) / 2 = n - 2 := by omega
    have hl5 : 5 ≤ 2 * n := (by omega); have hd5 : ¬ 2 ∣ (2 * n) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 := (by omega); have hd0 : ¬ 2 ∣ (2 * n + 1) := by omega
    have hl1 : 1 ≤ 2 * n + 1 := (by omega); have hd1 : 2 ∣ (2 * n + 1) - 1 := (by omega); have hq1 : ((2 * n + 1) - 1) / 2 = n - 0 := by omega
    have hl2 : 2 ≤ 2 * n + 1 := (by omega); have hd2 : ¬ 2 ∣ (2 * n + 1) - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 := (by omega); have hd3 : 2 ∣ (2 * n + 1) - 3 := (by omega); have hq3 : ((2 * n + 1) - 3) / 2 = n - 1 := by omega
    have hl4 : 4 ≤ 2 * n + 1 := (by omega); have hd4 : ¬ 2 ∣ (2 * n + 1) - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 := (by omega); have hd5 : 2 ∣ (2 * n + 1) - 5 := (by omega); have hq5 : ((2 * n + 1) - 5) / 2 = n - 2 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 1 := (by omega); have hd0 : ¬ 2 ∣ (2 * n - 1) := by omega
    have hl1 : 1 ≤ 2 * n - 1 := (by omega); have hd1 : 2 ∣ (2 * n - 1) - 1 := (by omega); have hq1 : ((2 * n - 1) - 1) / 2 = n - 1 := by omega
    have hl2 : 2 ≤ 2 * n - 1 := (by omega); have hd2 : ¬ 2 ∣ (2 * n - 1) - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 1 := (by omega); have hd3 : 2 ∣ (2 * n - 1) - 3 := (by omega); have hq3 : ((2 * n - 1) - 3) / 2 = n - 2 := by omega
    have hl4 : 4 ≤ 2 * n - 1 := (by omega); have hd4 : ¬ 2 ∣ (2 * n - 1) - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 1 := (by omega); have hd5 : 2 ∣ (2 * n - 1) - 5 := (by omega); have hq5 : ((2 * n - 1) - 5) / 2 = n - 3 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 1 := (by omega); have hd0 : 2 ∣ (2 * n + 1 - 1) := (by omega); have hq0 : ((2 * n + 1 - 1)) / 2 = n - 0 := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 1 := (by omega); have hd1 : ¬ 2 ∣ (2 * n + 1 - 1) - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 1 := (by omega); have hd2 : 2 ∣ (2 * n + 1 - 1) - 2 := (by omega); have hq2 : ((2 * n + 1 - 1) - 2) / 2 = n - 1 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 1 := (by omega); have hd3 : ¬ 2 ∣ (2 * n + 1 - 1) - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 1 := (by omega); have hd4 : 2 ∣ (2 * n + 1 - 1) - 4 := (by omega); have hq4 : ((2 * n + 1 - 1) - 4) / 2 = n - 2 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 1 := (by omega); have hd5 : ¬ 2 ∣ (2 * n + 1 - 1) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 2 := (by omega); have hd0 : 2 ∣ (2 * n - 2) := (by omega); have hq0 : ((2 * n - 2)) / 2 = n - 1 := by omega
    have hl1 : 1 ≤ 2 * n - 2 := (by omega); have hd1 : ¬ 2 ∣ (2 * n - 2) - 1 := by omega
    have hl2 : 2 ≤ 2 * n - 2 := (by omega); have hd2 : 2 ∣ (2 * n - 2) - 2 := (by omega); have hq2 : ((2 * n - 2) - 2) / 2 = n - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 2 := (by omega); have hd3 : ¬ 2 ∣ (2 * n - 2) - 3 := by omega
    have hl4 : 4 ≤ 2 * n - 2 := (by omega); have hd4 : 2 ∣ (2 * n - 2) - 4 := (by omega); have hq4 : ((2 * n - 2) - 4) / 2 = n - 3 := by omega
    have hl5 : 5 ≤ 2 * n - 2 := (by omega); have hd5 : ¬ 2 ∣ (2 * n - 2) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 2 := (by omega); have hd0 : ¬ 2 ∣ (2 * n + 1 - 2) := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 2 := (by omega); have hd1 : 2 ∣ (2 * n + 1 - 2) - 1 := (by omega); have hq1 : ((2 * n + 1 - 2) - 1) / 2 = n - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 2 := (by omega); have hd2 : ¬ 2 ∣ (2 * n + 1 - 2) - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 2 := (by omega); have hd3 : 2 ∣ (2 * n + 1 - 2) - 3 := (by omega); have hq3 : ((2 * n + 1 - 2) - 3) / 2 = n - 2 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 2 := (by omega); have hd4 : ¬ 2 ∣ (2 * n + 1 - 2) - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 2 := (by omega); have hd5 : 2 ∣ (2 * n + 1 - 2) - 5 := (by omega); have hq5 : ((2 * n + 1 - 2) - 5) / 2 = n - 3 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 3 := (by omega); have hd0 : ¬ 2 ∣ (2 * n - 3) := by omega
    have hl1 : 1 ≤ 2 * n - 3 := (by omega); have hd1 : 2 ∣ (2 * n - 3) - 1 := (by omega); have hq1 : ((2 * n - 3) - 1) / 2 = n - 2 := by omega
    have hl2 : 2 ≤ 2 * n - 3 := (by omega); have hd2 : ¬ 2 ∣ (2 * n - 3) - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 3 := (by omega); have hd3 : 2 ∣ (2 * n - 3) - 3 := (by omega); have hq3 : ((2 * n - 3) - 3) / 2 = n - 3 := by omega
    have hl4 : 4 ≤ 2 * n - 3 := (by omega); have hd4 : ¬ 2 ∣ (2 * n - 3) - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 3 := (by omega); have hd5 : 2 ∣ (2 * n - 3) - 5 := (by omega); have hq5 : ((2 * n - 3) - 5) / 2 = n - 4 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 3 := (by omega); have hd0 : 2 ∣ (2 * n + 1 - 3) := (by omega); have hq0 : ((2 * n + 1 - 3)) / 2 = n - 1 := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 3 := (by omega); have hd1 : ¬ 2 ∣ (2 * n + 1 - 3) - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 3 := (by omega); have hd2 : 2 ∣ (2 * n + 1 - 3) - 2 := (by omega); have hq2 : ((2 * n + 1 - 3) - 2) / 2 = n - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 3 := (by omega); have hd3 : ¬ 2 ∣ (2 * n + 1 - 3) - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 3 := (by omega); have hd4 : 2 ∣ (2 * n + 1 - 3) - 4 := (by omega); have hq4 : ((2 * n + 1 - 3) - 4) / 2 = n - 3 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 3 := (by omega); have hd5 : ¬ 2 ∣ (2 * n + 1 - 3) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 4 := (by omega); have hd0 : 2 ∣ (2 * n - 4) := (by omega); have hq0 : ((2 * n - 4)) / 2 = n - 2 := by omega
    have hl1 : 1 ≤ 2 * n - 4 := (by omega); have hd1 : ¬ 2 ∣ (2 * n - 4) - 1 := by omega
    have hl2 : 2 ≤ 2 * n - 4 := (by omega); have hd2 : 2 ∣ (2 * n - 4) - 2 := (by omega); have hq2 : ((2 * n - 4) - 2) / 2 = n - 3 := by omega
    have hl3 : 3 ≤ 2 * n - 4 := (by omega); have hd3 : ¬ 2 ∣ (2 * n - 4) - 3 := by omega
    have hl4 : 4 ≤ 2 * n - 4 := (by omega); have hd4 : 2 ∣ (2 * n - 4) - 4 := (by omega); have hq4 : ((2 * n - 4) - 4) / 2 = n - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 4 := (by omega); have hd5 : ¬ 2 ∣ (2 * n - 4) - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 4 := (by omega); have hd0 : ¬ 2 ∣ (2 * n + 1 - 4) := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 4 := (by omega); have hd1 : 2 ∣ (2 * n + 1 - 4) - 1 := (by omega); have hq1 : ((2 * n + 1 - 4) - 1) / 2 = n - 2 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 4 := (by omega); have hd2 : ¬ 2 ∣ (2 * n + 1 - 4) - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 4 := (by omega); have hd3 : 2 ∣ (2 * n + 1 - 4) - 3 := (by omega); have hq3 : ((2 * n + 1 - 4) - 3) / 2 = n - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 4 := (by omega); have hd4 : ¬ 2 ∣ (2 * n + 1 - 4) - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 4 := (by omega); have hd5 : 2 ∣ (2 * n + 1 - 4) - 5 := (by omega); have hq5 : ((2 * n + 1 - 4) - 5) / 2 = n - 4 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
private theorem state_step_dim6 (a0 a1 a2 a3 a4 a5 a6 : ℤ) (n : ℕ) (hn : 6 ≤ n) (b : Bool) :
    state 6 [a0, a1, a2, a3, a4, a5, a6] (2 * n + (if b then 1 else 0)) =
      (stateMatrix 6 [a0, a1, a2, a3, a4, a5, a6] b).mulVec (state 6 [a0, a1, a2, a3, a4, a5, a6] n) := by
  ext i
  fin_cases i <;> cases b
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n := (by omega); have hd0 : 2 ∣ (2 * n) := (by omega); have hq0 : ((2 * n)) / 2 = n - 0 := by omega
    have hl1 : 1 ≤ 2 * n := (by omega); have hd1 : ¬ 2 ∣ (2 * n) - 1 := by omega
    have hl2 : 2 ≤ 2 * n := (by omega); have hd2 : 2 ∣ (2 * n) - 2 := (by omega); have hq2 : ((2 * n) - 2) / 2 = n - 1 := by omega
    have hl3 : 3 ≤ 2 * n := (by omega); have hd3 : ¬ 2 ∣ (2 * n) - 3 := by omega
    have hl4 : 4 ≤ 2 * n := (by omega); have hd4 : 2 ∣ (2 * n) - 4 := (by omega); have hq4 : ((2 * n) - 4) / 2 = n - 2 := by omega
    have hl5 : 5 ≤ 2 * n := (by omega); have hd5 : ¬ 2 ∣ (2 * n) - 5 := by omega
    have hl6 : 6 ≤ 2 * n := (by omega); have hd6 : 2 ∣ (2 * n) - 6 := (by omega); have hq6 : ((2 * n) - 6) / 2 = n - 3 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5,hl6,hd6,hq6, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 := (by omega); have hd0 : ¬ 2 ∣ (2 * n + 1) := by omega
    have hl1 : 1 ≤ 2 * n + 1 := (by omega); have hd1 : 2 ∣ (2 * n + 1) - 1 := (by omega); have hq1 : ((2 * n + 1) - 1) / 2 = n - 0 := by omega
    have hl2 : 2 ≤ 2 * n + 1 := (by omega); have hd2 : ¬ 2 ∣ (2 * n + 1) - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 := (by omega); have hd3 : 2 ∣ (2 * n + 1) - 3 := (by omega); have hq3 : ((2 * n + 1) - 3) / 2 = n - 1 := by omega
    have hl4 : 4 ≤ 2 * n + 1 := (by omega); have hd4 : ¬ 2 ∣ (2 * n + 1) - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 := (by omega); have hd5 : 2 ∣ (2 * n + 1) - 5 := (by omega); have hq5 : ((2 * n + 1) - 5) / 2 = n - 2 := by omega
    have hl6 : 6 ≤ 2 * n + 1 := (by omega); have hd6 : ¬ 2 ∣ (2 * n + 1) - 6 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5,hl6,hd6, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 1 := (by omega); have hd0 : ¬ 2 ∣ (2 * n - 1) := by omega
    have hl1 : 1 ≤ 2 * n - 1 := (by omega); have hd1 : 2 ∣ (2 * n - 1) - 1 := (by omega); have hq1 : ((2 * n - 1) - 1) / 2 = n - 1 := by omega
    have hl2 : 2 ≤ 2 * n - 1 := (by omega); have hd2 : ¬ 2 ∣ (2 * n - 1) - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 1 := (by omega); have hd3 : 2 ∣ (2 * n - 1) - 3 := (by omega); have hq3 : ((2 * n - 1) - 3) / 2 = n - 2 := by omega
    have hl4 : 4 ≤ 2 * n - 1 := (by omega); have hd4 : ¬ 2 ∣ (2 * n - 1) - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 1 := (by omega); have hd5 : 2 ∣ (2 * n - 1) - 5 := (by omega); have hq5 : ((2 * n - 1) - 5) / 2 = n - 3 := by omega
    have hl6 : 6 ≤ 2 * n - 1 := (by omega); have hd6 : ¬ 2 ∣ (2 * n - 1) - 6 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5,hl6,hd6, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 1 := (by omega); have hd0 : 2 ∣ (2 * n + 1 - 1) := (by omega); have hq0 : ((2 * n + 1 - 1)) / 2 = n - 0 := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 1 := (by omega); have hd1 : ¬ 2 ∣ (2 * n + 1 - 1) - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 1 := (by omega); have hd2 : 2 ∣ (2 * n + 1 - 1) - 2 := (by omega); have hq2 : ((2 * n + 1 - 1) - 2) / 2 = n - 1 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 1 := (by omega); have hd3 : ¬ 2 ∣ (2 * n + 1 - 1) - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 1 := (by omega); have hd4 : 2 ∣ (2 * n + 1 - 1) - 4 := (by omega); have hq4 : ((2 * n + 1 - 1) - 4) / 2 = n - 2 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 1 := (by omega); have hd5 : ¬ 2 ∣ (2 * n + 1 - 1) - 5 := by omega
    have hl6 : 6 ≤ 2 * n + 1 - 1 := (by omega); have hd6 : 2 ∣ (2 * n + 1 - 1) - 6 := (by omega); have hq6 : ((2 * n + 1 - 1) - 6) / 2 = n - 3 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5,hl6,hd6,hq6, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 2 := (by omega); have hd0 : 2 ∣ (2 * n - 2) := (by omega); have hq0 : ((2 * n - 2)) / 2 = n - 1 := by omega
    have hl1 : 1 ≤ 2 * n - 2 := (by omega); have hd1 : ¬ 2 ∣ (2 * n - 2) - 1 := by omega
    have hl2 : 2 ≤ 2 * n - 2 := (by omega); have hd2 : 2 ∣ (2 * n - 2) - 2 := (by omega); have hq2 : ((2 * n - 2) - 2) / 2 = n - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 2 := (by omega); have hd3 : ¬ 2 ∣ (2 * n - 2) - 3 := by omega
    have hl4 : 4 ≤ 2 * n - 2 := (by omega); have hd4 : 2 ∣ (2 * n - 2) - 4 := (by omega); have hq4 : ((2 * n - 2) - 4) / 2 = n - 3 := by omega
    have hl5 : 5 ≤ 2 * n - 2 := (by omega); have hd5 : ¬ 2 ∣ (2 * n - 2) - 5 := by omega
    have hl6 : 6 ≤ 2 * n - 2 := (by omega); have hd6 : 2 ∣ (2 * n - 2) - 6 := (by omega); have hq6 : ((2 * n - 2) - 6) / 2 = n - 4 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5,hl6,hd6,hq6, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 2 := (by omega); have hd0 : ¬ 2 ∣ (2 * n + 1 - 2) := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 2 := (by omega); have hd1 : 2 ∣ (2 * n + 1 - 2) - 1 := (by omega); have hq1 : ((2 * n + 1 - 2) - 1) / 2 = n - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 2 := (by omega); have hd2 : ¬ 2 ∣ (2 * n + 1 - 2) - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 2 := (by omega); have hd3 : 2 ∣ (2 * n + 1 - 2) - 3 := (by omega); have hq3 : ((2 * n + 1 - 2) - 3) / 2 = n - 2 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 2 := (by omega); have hd4 : ¬ 2 ∣ (2 * n + 1 - 2) - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 2 := (by omega); have hd5 : 2 ∣ (2 * n + 1 - 2) - 5 := (by omega); have hq5 : ((2 * n + 1 - 2) - 5) / 2 = n - 3 := by omega
    have hl6 : 6 ≤ 2 * n + 1 - 2 := (by omega); have hd6 : ¬ 2 ∣ (2 * n + 1 - 2) - 6 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5,hl6,hd6, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 3 := (by omega); have hd0 : ¬ 2 ∣ (2 * n - 3) := by omega
    have hl1 : 1 ≤ 2 * n - 3 := (by omega); have hd1 : 2 ∣ (2 * n - 3) - 1 := (by omega); have hq1 : ((2 * n - 3) - 1) / 2 = n - 2 := by omega
    have hl2 : 2 ≤ 2 * n - 3 := (by omega); have hd2 : ¬ 2 ∣ (2 * n - 3) - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 3 := (by omega); have hd3 : 2 ∣ (2 * n - 3) - 3 := (by omega); have hq3 : ((2 * n - 3) - 3) / 2 = n - 3 := by omega
    have hl4 : 4 ≤ 2 * n - 3 := (by omega); have hd4 : ¬ 2 ∣ (2 * n - 3) - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 3 := (by omega); have hd5 : 2 ∣ (2 * n - 3) - 5 := (by omega); have hq5 : ((2 * n - 3) - 5) / 2 = n - 4 := by omega
    have hl6 : 6 ≤ 2 * n - 3 := (by omega); have hd6 : ¬ 2 ∣ (2 * n - 3) - 6 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5,hl6,hd6, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 3 := (by omega); have hd0 : 2 ∣ (2 * n + 1 - 3) := (by omega); have hq0 : ((2 * n + 1 - 3)) / 2 = n - 1 := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 3 := (by omega); have hd1 : ¬ 2 ∣ (2 * n + 1 - 3) - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 3 := (by omega); have hd2 : 2 ∣ (2 * n + 1 - 3) - 2 := (by omega); have hq2 : ((2 * n + 1 - 3) - 2) / 2 = n - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 3 := (by omega); have hd3 : ¬ 2 ∣ (2 * n + 1 - 3) - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 3 := (by omega); have hd4 : 2 ∣ (2 * n + 1 - 3) - 4 := (by omega); have hq4 : ((2 * n + 1 - 3) - 4) / 2 = n - 3 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 3 := (by omega); have hd5 : ¬ 2 ∣ (2 * n + 1 - 3) - 5 := by omega
    have hl6 : 6 ≤ 2 * n + 1 - 3 := (by omega); have hd6 : 2 ∣ (2 * n + 1 - 3) - 6 := (by omega); have hq6 : ((2 * n + 1 - 3) - 6) / 2 = n - 4 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5,hl6,hd6,hq6, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 4 := (by omega); have hd0 : 2 ∣ (2 * n - 4) := (by omega); have hq0 : ((2 * n - 4)) / 2 = n - 2 := by omega
    have hl1 : 1 ≤ 2 * n - 4 := (by omega); have hd1 : ¬ 2 ∣ (2 * n - 4) - 1 := by omega
    have hl2 : 2 ≤ 2 * n - 4 := (by omega); have hd2 : 2 ∣ (2 * n - 4) - 2 := (by omega); have hq2 : ((2 * n - 4) - 2) / 2 = n - 3 := by omega
    have hl3 : 3 ≤ 2 * n - 4 := (by omega); have hd3 : ¬ 2 ∣ (2 * n - 4) - 3 := by omega
    have hl4 : 4 ≤ 2 * n - 4 := (by omega); have hd4 : 2 ∣ (2 * n - 4) - 4 := (by omega); have hq4 : ((2 * n - 4) - 4) / 2 = n - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 4 := (by omega); have hd5 : ¬ 2 ∣ (2 * n - 4) - 5 := by omega
    have hl6 : 6 ≤ 2 * n - 4 := (by omega); have hd6 : 2 ∣ (2 * n - 4) - 6 := (by omega); have hq6 : ((2 * n - 4) - 6) / 2 = n - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5,hl6,hd6,hq6, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 4 := (by omega); have hd0 : ¬ 2 ∣ (2 * n + 1 - 4) := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 4 := (by omega); have hd1 : 2 ∣ (2 * n + 1 - 4) - 1 := (by omega); have hq1 : ((2 * n + 1 - 4) - 1) / 2 = n - 2 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 4 := (by omega); have hd2 : ¬ 2 ∣ (2 * n + 1 - 4) - 2 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 4 := (by omega); have hd3 : 2 ∣ (2 * n + 1 - 4) - 3 := (by omega); have hq3 : ((2 * n + 1 - 4) - 3) / 2 = n - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 4 := (by omega); have hd4 : ¬ 2 ∣ (2 * n + 1 - 4) - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 4 := (by omega); have hd5 : 2 ∣ (2 * n + 1 - 4) - 5 := (by omega); have hq5 : ((2 * n + 1 - 4) - 5) / 2 = n - 4 := by omega
    have hl6 : 6 ≤ 2 * n + 1 - 4 := (by omega); have hd6 : ¬ 2 ∣ (2 * n + 1 - 4) - 6 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5,hl6,hd6, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n - 5 := (by omega); have hd0 : ¬ 2 ∣ (2 * n - 5) := by omega
    have hl1 : 1 ≤ 2 * n - 5 := (by omega); have hd1 : 2 ∣ (2 * n - 5) - 1 := (by omega); have hq1 : ((2 * n - 5) - 1) / 2 = n - 3 := by omega
    have hl2 : 2 ≤ 2 * n - 5 := (by omega); have hd2 : ¬ 2 ∣ (2 * n - 5) - 2 := by omega
    have hl3 : 3 ≤ 2 * n - 5 := (by omega); have hd3 : 2 ∣ (2 * n - 5) - 3 := (by omega); have hq3 : ((2 * n - 5) - 3) / 2 = n - 4 := by omega
    have hl4 : 4 ≤ 2 * n - 5 := (by omega); have hd4 : ¬ 2 ∣ (2 * n - 5) - 4 := by omega
    have hl5 : 5 ≤ 2 * n - 5 := (by omega); have hd5 : 2 ∣ (2 * n - 5) - 5 := (by omega); have hq5 : ((2 * n - 5) - 5) / 2 = n - 5 := by omega
    have hl6 : 6 ≤ 2 * n - 5 := (by omega); have hd6 : ¬ 2 ∣ (2 * n - 5) - 6 := by omega
    simp only [hl0,hd0,hl1,hd1,hq1,hl2,hd2,hl3,hd3,hq3,hl4,hd4,hl5,hd5,hq5,hl6,hd6, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
  · simp only [state, Fin.val_mk, Bool.false_eq_true, eq_self_iff_true, if_false, if_true, Nat.sub_zero]
    rw [recur_pos _ _ (by omega)]
    simp only [p, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero]
    have hl0 : 0 ≤ 2 * n + 1 - 5 := (by omega); have hd0 : 2 ∣ (2 * n + 1 - 5) := (by omega); have hq0 : ((2 * n + 1 - 5)) / 2 = n - 2 := by omega
    have hl1 : 1 ≤ 2 * n + 1 - 5 := (by omega); have hd1 : ¬ 2 ∣ (2 * n + 1 - 5) - 1 := by omega
    have hl2 : 2 ≤ 2 * n + 1 - 5 := (by omega); have hd2 : 2 ∣ (2 * n + 1 - 5) - 2 := (by omega); have hq2 : ((2 * n + 1 - 5) - 2) / 2 = n - 3 := by omega
    have hl3 : 3 ≤ 2 * n + 1 - 5 := (by omega); have hd3 : ¬ 2 ∣ (2 * n + 1 - 5) - 3 := by omega
    have hl4 : 4 ≤ 2 * n + 1 - 5 := (by omega); have hd4 : 2 ∣ (2 * n + 1 - 5) - 4 := (by omega); have hq4 : ((2 * n + 1 - 5) - 4) / 2 = n - 4 := by omega
    have hl5 : 5 ≤ 2 * n + 1 - 5 := (by omega); have hd5 : ¬ 2 ∣ (2 * n + 1 - 5) - 5 := by omega
    have hl6 : 6 ≤ 2 * n + 1 - 5 := (by omega); have hd6 : 2 ∣ (2 * n + 1 - 5) - 6 := (by omega); have hq6 : ((2 * n + 1 - 5) - 6) / 2 = n - 5 := by omega
    simp only [hl0,hd0,hq0,hl1,hd1,hl2,hd2,hq2,hl3,hd3,hl4,hd4,hq4,hl5,hd5,hl6,hd6,hq6, and_true, and_false, if_true, if_false, Nat.sub_zero]
    norm_num [p, stateMatrix, pz, List.getD, state, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Finset.sum_range_succ]
    simp_all [state, Int.toNat, Nat.dvd_iff_mod_eq_zero, Nat.mul_comm]
    <;> (try split_ifs) <;> first | omega | ring
private theorem state_step_1 (n : ℕ) (hn : 6 ≤ n) (b : Bool) :
    state 5 (p 1) (2 * n + (if b then 1 else 0)) =
      (stateMatrix 5 (p 1) b).mulVec (state 5 (p 1) n) := by
  simpa only [p] using state_step_dim5 (1) (3) (2) (-2) (-3) (-1) n hn b
private theorem state_step_2 (n : ℕ) (hn : 6 ≤ n) (b : Bool) :
    state 5 (p 2) (2 * n + (if b then 1 else 0)) =
      (stateMatrix 5 (p 2) b).mulVec (state 5 (p 2) n) := by
  simpa only [p] using state_step_dim5 (1) (1) (-2) (-2) (1) (1) n hn b
private theorem state_step_3 (n : ℕ) (hn : 6 ≤ n) (b : Bool) :
    state 5 (p 3) (2 * n + (if b then 1 else 0)) =
      (stateMatrix 5 (p 3) b).mulVec (state 5 (p 3) n) := by
  simpa only [p] using state_step_dim5 (1) (-1) (-2) (2) (1) (-1) n hn b
open Finset Matrix
def stateZ (d : ℕ) (q : List ℤ) (n : ℕ) : Fin d → ℤ :=
  fun i => zrecur q ((n : ℤ) - (i : ℕ))
theorem stateZ_eq_state (d : ℕ) (hd : d ≤ 6) (q : List ℤ) (n : ℕ) (hn : 6 ≤ n) :
    stateZ d q n = state d q n := by
  ext i
  have hi := i.isLt
  simp only [stateZ, state, zrecur]
  rw [if_pos (by omega), Int.toNat_sub]
theorem stateZ_step_1 (n : ℕ) (b : Bool) :
    stateZ 5 (p 1) (2*n+(if b then 1 else 0)) =
      (stateMatrix 5 (p 1) b).mulVec (stateZ 5 (p 1) n) := by
  by_cases hn : n < 6
  · interval_cases n <;> cases b <;> ext i <;> fin_cases i <;> decide +kernel
  · have hl : 6 ≤ n := by omega
    rw [stateZ_eq_state 5 (by decide) (p 1) n hl,
      stateZ_eq_state 5 (by decide) (p 1) _ (by omega)]
    exact state_step_1 n hl b
theorem stateZ_step_2 (n : ℕ) (b : Bool) :
    stateZ 5 (p 2) (2*n+(if b then 1 else 0)) =
      (stateMatrix 5 (p 2) b).mulVec (stateZ 5 (p 2) n) := by
  by_cases hn : n < 6
  · interval_cases n <;> cases b <;> ext i <;> fin_cases i <;> decide +kernel
  · have hl : 6 ≤ n := by omega
    rw [stateZ_eq_state 5 (by decide) (p 2) n hl,
      stateZ_eq_state 5 (by decide) (p 2) _ (by omega)]
    exact state_step_2 n hl b
theorem stateZ_step_3 (n : ℕ) (b : Bool) :
    stateZ 5 (p 3) (2*n+(if b then 1 else 0)) =
      (stateMatrix 5 (p 3) b).mulVec (stateZ 5 (p 3) n) := by
  by_cases hn : n < 6
  · interval_cases n <;> cases b <;> ext i <;> fin_cases i <;> decide +kernel
  · have hl : 6 ≤ n := by omega
    rw [stateZ_eq_state 5 (by decide) (p 3) n hl,
      stateZ_eq_state 5 (by decide) (p 3) _ (by omega)]
    exact state_step_3 n hl b
def appendValue (q : ℕ) (w : List Bool) : ℕ :=
  Nat.ofDigits 2 (w.map Bool.toNat ++ [q])
theorem state_word {d : ℕ} (q : List ℤ) (M : Bool → Matrix (Fin d) (Fin d) ℤ)
    (step : ∀ n, ∀ b, stateZ d q (2*n+(if b then 1 else 0)) = (M b).mulVec (stateZ d q n))
    (p : ℕ) (w : List Bool) :
    stateZ d q (appendValue p w) = (wordMatrix M w).mulVec (stateZ d q p) := by
  have hdigits : appendValue p w = w.foldr (fun b n => 2*n+(if b then 1 else 0)) p := by
    simp only [appendValue, Nat.ofDigits_eq_foldr, List.foldr_append, List.foldr_map,
      List.foldr_cons, List.foldr_nil, Nat.cast_id, mul_zero, add_zero]
    congr 1
    funext b n
    cases b <;> simp [Bool.toNat, Nat.add_comm]
  have hstate := List.foldr_hom (stateZ d q)
    (g₁ := fun b n => 2*n+(if b then 1 else 0))
    (g₂ := fun b v => (M b).mulVec v) (l := w) (init := p)
    (fun b n => (step n b).symm)
  have hmatrix := List.foldr_hom
    (fun A : Matrix (Fin d) (Fin d) ℤ => A.mulVec (stateZ d q p))
    (g₁ := fun b A => M b * A) (g₂ := fun b v => (M b).mulVec v)
    (l := w) (init := 1)
    (fun b A => Matrix.mulVec_mulVec (stateZ d q p) (M b) A)
  rw [hdigits]
  exact hstate.symm.trans (by simpa only [wordMatrix, List.prod_eq_foldr,
    List.foldr_map, Matrix.one_mulVec] using hmatrix)
theorem vector_prefix_bound {d : ℕ} (q : List ℤ) (M : Bool → Matrix (Fin d) (Fin d) ℤ)
    (step : ∀ n, ∀ b, stateZ d q (2*n+(if b then 1 else 0)) = (M b).mulVec (stateZ d q n))
    (K : ℕ) (norm : ∀ w, matrixBound (wordMatrix M w) (K * 16 ^ w.length))
    (p : ℕ) (w : List Bool) (B : ℕ) (seed : vectorBound (stateZ d q p) B) :
    vectorBound (stateZ d q (appendValue p w)) (K * 16 ^ w.length * B) := by
  rw [state_word q M step p w]
  exact matrix_apply_bound _ _ _ _ (norm w) seed
private theorem state_step_4 (n : ℕ) (hn : 6 ≤ n) (b : Bool) :
    state 5 (p 4) (2 * n + (if b then 1 else 0)) =
      (stateMatrix 5 (p 4) b).mulVec (state 5 (p 4) n) := by
  simpa only [p] using state_step_dim5 (1) (-3) (2) (2) (-3) (1) n hn b
private theorem state_step_5 (n : ℕ) (hn : 6 ≤ n) (b : Bool) :
    state 5 (p 5) (2 * n + (if b then 1 else 0)) =
      (stateMatrix 5 (p 5) b).mulVec (state 5 (p 5) n) := by
  simpa only [p] using state_step_dim5 (1) (-5) (10) (-10) (5) (-1) n hn b
private theorem state_step_6 (n : ℕ) (hn : 6 ≤ n) (b : Bool) :
    state 6 (p 6) (2 * n + (if b then 1 else 0)) =
      (stateMatrix 6 (p 6) b).mulVec (state 6 (p 6) n) := by
  simpa only [p] using state_step_dim6 (1) (-6) (15) (-20) (15) (-6) (1) n hn b
theorem stateZ_step_4 (n : ℕ) (b : Bool) :
    stateZ 5 (p 4) (2*n+(if b then 1 else 0)) =
      (stateMatrix 5 (p 4) b).mulVec (stateZ 5 (p 4) n) := by
  by_cases hn : n < 6
  · interval_cases n <;> cases b <;> ext i <;> fin_cases i <;> decide +kernel
  · have hl : 6 ≤ n := by omega
    rw [stateZ_eq_state 5 (by decide) (p 4) n hl,
      stateZ_eq_state 5 (by decide) (p 4) _ (by omega)]
    exact state_step_4 n hl b
theorem stateZ_step_5 (n : ℕ) (b : Bool) :
    stateZ 5 (p 5) (2*n+(if b then 1 else 0)) =
      (stateMatrix 5 (p 5) b).mulVec (stateZ 5 (p 5) n) := by
  by_cases hn : n < 6
  · interval_cases n <;> cases b <;> ext i <;> fin_cases i <;> decide +kernel
  · have hl : 6 ≤ n := by omega
    rw [stateZ_eq_state 5 (by decide) (p 5) n hl,
      stateZ_eq_state 5 (by decide) (p 5) _ (by omega)]
    exact state_step_5 n hl b
theorem stateZ_step_6 (n : ℕ) (b : Bool) :
    stateZ 6 (p 6) (2*n+(if b then 1 else 0)) =
      (stateMatrix 6 (p 6) b).mulVec (stateZ 6 (p 6) n) := by
  by_cases hn : n < 6
  · interval_cases n <;> cases b <;> ext i <;> fin_cases i <;> decide +kernel
  · have hl : 6 ≤ n := by omega
    rw [stateZ_eq_state 6 (by decide) (p 6) n hl,
      stateZ_eq_state 6 (by decide) (p 6) _ (by omega)]
    exact state_step_6 n hl b
theorem appendValue_decompose (p0 : ℕ) (w : List Bool) :
    appendValue p0 w = p0 * 2 ^ w.length + appendValue 0 w := by
  simp only [appendValue, Nat.ofDigits_append, Nat.ofDigits_singleton, List.length_map,
    mul_zero, add_zero]
  ring
theorem lowWord_bound (w : List Bool) : appendValue 0 w < 2 ^ w.length := by
  simp only [appendValue, Nat.ofDigits_append, Nat.ofDigits_singleton, List.length_map,
    mul_zero, add_zero]
  have hd : ∀ d ∈ w.map Bool.toNat, d < 2 := by
    intro d hd
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hd
    cases b <;> decide
  simpa only [List.length_map] using
    Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2) hd
theorem word_for_low (m low : ℕ) (hlow : low < 2 ^ m) :
    ∃ w : List Bool, w.length = m ∧ appendValue 0 w = low := by
  refine ⟨(Nat.digitsAppend 2 m low).map (fun d => decide (d = 1)), ?_, ?_⟩
  · simpa only [List.length_map] using Nat.length_digitsAppend (by decide : 1 < 2) m hlow
  · simp only [appendValue, Nat.ofDigits_append_zero, List.map_map, Function.comp_def]
    have hd : (Nat.digitsAppend 2 m low).map (fun d => (decide (d = 1)).toNat) =
        Nat.digitsAppend 2 m low := by
      conv_rhs => rw [← List.map_id (Nat.digitsAppend 2 m low)]
      apply List.map_congr_left
      intro d hd
      have := Nat.lt_of_mem_digitsAppend (by decide : 1 < 2) m d hd
      interval_cases d <;> rfl
    rw [hd]
    exact (Nat.setInvOn_digitsAppend_ofDigits (by decide : 1 < 2) m).2 hlow
theorem state_dyadic_bound {d : ℕ} (q : List ℤ) (M : Bool → Matrix (Fin d) (Fin d) ℤ)
    (step : ∀ n b, stateZ d q (2*n+(if b then 1 else 0)) = (M b).mulVec (stateZ d q n))
    (K : ℕ) (norm : ∀ w, matrixBound (wordMatrix M w) (K * 16 ^ w.length))
    (p0 m low : ℕ) (hlow : low < 2 ^ m) :
    vectorBound (stateZ d q (p0*2^m+low))
      (K * 16 ^ m * (Finset.range d).sup (fun i => (zrecur q ((p0:ℤ)-i)).natAbs)) := by
  obtain ⟨w,hw,hv⟩ := word_for_low m low hlow
  have hs : vectorBound (stateZ d q p0)
      ((Finset.range d).sup (fun i => (zrecur q ((p0:ℤ)-i)).natAbs)) := by
    intro i
    exact Finset.le_sup (s := Finset.range d) (b := i.val)
      (f := fun a => (zrecur q ((p0:ℤ)-a)).natAbs) (Finset.mem_range.mpr i.isLt)
  have hb := vector_prefix_bound q M step K norm p0 w _ hs
  rw [appendValue_decompose, hw, hv] at hb
  exact hb
end D5.S1.Words.EvilOdious.SequenceCoefficients
