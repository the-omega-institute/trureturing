/- GID: D5/S3/Combinatorics/TraceArrays/HardinA185858
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceArrays/HardinA185858
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hardin-Barker A185858: exact array-count generating function and radical formula. -/

/-
proof_shape: result: bind-only; generic finite-cardinality equivalences, finite-sum
  identities, coefficient extensionality and linear-recurrence uniqueness, with
  algebraic normalization after expanding the same-module helpers.
escape_witness: none
admission_basis: open-problem-resolution (#22162; Proved)
Direct frozen dependencies: none (pinned Mathlib only).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22308

The binary arrays, ordinary contiguous-block trace, adjacent-block inequality,
rational normalization and zero constant coefficient are the source's objects.
The source is OEIS A185858, NAME and FORMULA, revision 9, offset 1.
The two conjectures occur in Colin Barker's FORMULA block; there is no source page number.
The binary-triple sum uses hammingNorm; the correspondence with the natural
entry sum is proved inside trace_bridge. The word predicate uses List.IsChain
on List.ofFn; trace words use the same existing chain predicate directly,
without a new alias.
The coordinate change uses Equiv.piComm, Equiv.piCongrRight, Equiv.arrowCongr,
Equiv.addRight, finSumFinEquiv and Equiv.sumArrowEquivProdArrow.
All implementation carriers are private. No type alias is introduced.

Private proof shapes and consumers (Direct frozen dependencies: none for every row):
  trace_bridge: bind-only; valid_bridge
  valid_bridge: bind-only; traceWord_valid
  totals_valid: bind-only; traceWord_valid, count_words
  traceWord_valid: bind-only; count_words
  triple_fiber: bind-only; word_fiber
  word_fiber: bind-only; array_fiber, count_words
  array_fiber: bind-only; count_words
  count_words: bind-only; count_recurrence, count_normalized
  suffix_zero: bind-only; suffix_symmetry, a_initial
  suffix_succ: bind-only; suffix_equations
  triple_univ: bind-only; sum_triple
  sum_triple: bind-only; word_card, suffix_equations
  word_card: bind-only; word_recurrence, count_normalized
  suffix_equations: bind-only; suffix_symmetry, word_recurrence, a_initial
  suffix_symmetry: content; count_normalized
  word_recurrence: bind-only; count_recurrence
  count_recurrence: bind-only; a_recurrence
  a_recurrence: bind-only; result
  count_normalized: content; a_initial
  a_initial: bind-only; result
  series_formula: bind-only; result
  radical_recurrence: bind-only; closed_formula
  radical_initial: bind-only; closed_formula
  closed_formula: bind-only; result
Every private theorem has escape_witness: none; the module uses its settling result.
The all-length symmetry induction is used in count_normalized. The scalar
recurrence also follows from the four transfer equations without that induction.
-/

import Mathlib.Algebra.LinearRecurrence
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.ChainOfFn
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.Real.Sqrt

namespace D5.S3.Combinatorics.TraceArrays.HardinA185858

/-- Ordinary trace of the contiguous 3 by 3 block with top row i.
The binary entries are coerced to natural numbers before taking the trace. -/
def blockTrace (n : ℕ) (B : Matrix (Fin (n + 2)) (Fin 3) (Fin 2))
    (i : Fin n) : ℕ :=
  Matrix.trace
    (Matrix.submatrix (fun r c => (B r c).val)
      (fun r : Fin 3 => (⟨i.val + r.val, by omega⟩ : Fin (n + 2))) id)

/-- Width three has exactly one block column, so all block neighbors are vertical. -/
def Valid (n : ℕ) (B : Matrix (Fin (n + 2)) (Fin 3) (Fin 2)) : Prop :=
  ∀ (i j : Fin n), j.val = i.val + 1 → blockTrace n B i ≠ blockTrace n B j

/-- Count literal arrays, with no quotient by symmetry. -/
noncomputable def count (n : ℕ) : ℕ :=
  Nat.card {B : Matrix (Fin (n + 2)) (Fin 3) (Fin 2) // Valid n B}

/-- The source normalization is rational division, not truncated natural division.
Only positive indices of this auxiliary definition occur in the claim. -/
noncomputable def a (n : ℕ) : ℚ := (count n : ℚ) / 128

/-- Offset one: there is no asserted source term a(0). -/
noncomputable def generatingSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else a n)

/-- The two formulas in Barker's conjecture block, with the positive-index domain explicit. -/
def claim : Prop :=
  generatingSeries =
    (2 * PowerSeries.X * (2 + 3 * PowerSeries.X)) *
      (1 - 4 * PowerSeries.X - 9 * PowerSeries.X ^ 2)⁻¹ ∧
  ∀ (n : ℕ), 1 ≤ n →
    (a n : ℝ) =
      (((2 - Real.sqrt 13) ^ n * (-4 + Real.sqrt 13) +
        (2 + Real.sqrt 13) ^ n * (4 + Real.sqrt 13)) / (3 * Real.sqrt 13))

end D5.S3.Combinatorics.TraceArrays.HardinA185858

namespace D5.S3.Combinatorics.TraceArrays.HardinA185858
open scoped BigOperators

private def WordValid (n : ℕ) (w : (Fin n → Fin 3 → Fin 2)) : Prop :=
  (List.ofFn w).IsChain (fun a b => hammingNorm a ≠ hammingNorm b)

private def arrayEquiv (n : ℕ) :
    Matrix (Fin (n+2)) (Fin 3) (Fin 2) ≃
      (Fin n → Fin 3 → Fin 2) × (Fin 2 → Fin 3 → Fin 2) :=
  (Equiv.piComm (fun _ : Fin (n+2) => fun _ : Fin 3 => Fin 2)).trans
    ((Equiv.piCongrRight (fun c : Fin 3 =>
      Equiv.arrowCongr
        (Equiv.addRight (⟨c.val % (n+2), Nat.mod_lt _ (by omega)⟩ : Fin (n+2))).symm
        (Equiv.refl (Fin 2)))).trans
      ((Equiv.piComm (fun _ : Fin 3 => fun _ : Fin (n+2) => Fin 2)).trans
        ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl (Fin 3 → Fin 2))).trans
          (Equiv.sumArrowEquivProdArrow (Fin n) (Fin 2) (Fin 3 → Fin 2)))))

private theorem trace_bridge (n : ℕ) (B : Matrix (Fin (n+2)) (Fin 3) (Fin 2))
    (i : Fin n) : blockTrace n B i = hammingNorm ((arrayEquiv n B).1 i) := by
  classical
  unfold blockTrace Matrix.trace hammingNorm
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  change (B ⟨i.val + c.val, _⟩ c).val =
    if (B (Fin.castAdd 2 i + (⟨c.val % (n+2), Nat.mod_lt _ (by omega)⟩ : Fin (n+2))) c) ≠ 0 then 1 else 0
  have he : (⟨i.val + c.val, by omega⟩ : Fin (n+2)) =
      Fin.castAdd 2 i + (⟨c.val % (n+2), Nat.mod_lt _ (by omega)⟩ : Fin (n+2)) := by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_castAdd]
    have hi := i.isLt
    have hc : c.val < n+2 := by omega
    have hs : i.val+c.val < n+2 := by omega
    rw [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hs]
  rw [he]
  have hlt := (B (Fin.castAdd 2 i + (⟨c.val % (n+2), Nat.mod_lt _ (by omega)⟩ : Fin (n+2))) c).isLt
  split_ifs with h
  · have hn : (B (Fin.castAdd 2 i + (⟨c.val % (n+2), Nat.mod_lt _ (by omega)⟩ : Fin (n+2))) c).val ≠ 0 := by
      exact Fin.val_ne_zero_iff.mpr h
    omega
  · have hz := Classical.not_not.mp h
    simp [hz]

private theorem valid_bridge (n : ℕ) (B : Matrix (Fin (n+2)) (Fin 3) (Fin 2)) :
    Valid n B ↔ WordValid n (arrayEquiv n B).1 := by
  simp only [Valid, WordValid, List.isChain_ofFn, trace_bridge]
  constructor
  · intro h i hi
    exact h ⟨i, by omega⟩ ⟨i+1, hi⟩ rfl
  · intro h i j hij
    have heq : j = ⟨i.val+1, by omega⟩ := Fin.ext hij
    simpa only [← heq] using h i.val (by omega)

end D5.S3.Combinatorics.TraceArrays.HardinA185858
namespace D5.S3.Combinatorics.TraceArrays.HardinA185858
open scoped BigOperators

private def totals (n : ℕ) (w : (Fin n → Fin 3 → Fin 2)) : Fin n → Fin 4 :=
  fun i => ⟨hammingNorm (w i), by simpa using Nat.lt_succ_of_le (hammingNorm_le_card_fintype (x := w i))⟩

private theorem totals_valid (n : ℕ) (w : (Fin n → Fin 3 → Fin 2)) :
    WordValid n w ↔ (List.ofFn (totals n w)).IsChain (· ≠ ·) := by
  simp [WordValid, List.isChain_ofFn, totals, Fin.ext_iff]

private theorem traceWord_valid (n : ℕ) (B : Matrix (Fin (n+2)) (Fin 3) (Fin 2)) :
    Valid n B ↔ (List.ofFn (totals n (arrayEquiv n B).1)).IsChain (· ≠ ·) := by
  exact (valid_bridge n B).trans (totals_valid n _)

private theorem triple_fiber (s : Fin 4) :
    Nat.card {t : (Fin 3 → Fin 2) // hammingNorm t = s.val} = Nat.choose 3 s.val := by
  rw [Nat.card_eq_fintype_card]
  revert s
  decide

private theorem word_fiber (n : ℕ) (s : Fin n → Fin 4) :
    Nat.card {w : (Fin n → Fin 3 → Fin 2) // totals n w = s} = ∏ i, Nat.choose 3 (s i).val := by
  let e : {w : (Fin n → Fin 3 → Fin 2) // totals n w = s} ≃
      {w : (Fin n → Fin 3 → Fin 2) // ∀ i, hammingNorm (w i) = (s i).val} :=
    Equiv.subtypeEquivRight (fun w => by simp [totals, funext_iff, Fin.ext_iff])
  rw [Nat.card_congr (e.trans (Equiv.subtypePiEquivPi (β := fun _ : Fin n => (Fin 3 → Fin 2)) (p := fun i t => hammingNorm t = (s i).val))), Nat.card_pi]
  exact Finset.prod_congr rfl (fun i _ => triple_fiber (s i))

private theorem array_fiber (n : ℕ) (s : Fin n → Fin 4) :
    Nat.card {B : Matrix (Fin (n+2)) (Fin 3) (Fin 2) // totals n (arrayEquiv n B).1 = s} =
      64 * ∏ i, Nat.choose 3 (s i).val := by
  let e : {B : Matrix (Fin (n+2)) (Fin 3) (Fin 2) // totals n (arrayEquiv n B).1 = s} ≃
      {p : (Fin n → Fin 3 → Fin 2) × (Fin 2 → Fin 3 → Fin 2) // totals n p.1 = s} :=
    (arrayEquiv n).subtypeEquiv (fun _ => Iff.rfl)
  rw [Nat.card_congr (e.trans (Equiv.prodSubtypeFstEquivSubtypeProd (α := (Fin n → Fin 3 → Fin 2)) (β := (Fin 2 → Fin 3 → Fin 2)) (p := fun w => totals n w = s))), Nat.card_prod,
    word_fiber]
  norm_num [Nat.card_fun, Nat.card_fin]
  omega

private theorem count_words (n : ℕ) :
    count n = 64 * Nat.card {w : (Fin n → Fin 3 → Fin 2) // WordValid n w} := by
  classical
  let := Fintype.ofFinite {s : Fin n → Fin 4 // (List.ofFn s).IsChain (· ≠ ·)}
  have ha : count n = ∑ s : {s : Fin n → Fin 4 // (List.ofFn s).IsChain (· ≠ ·)},
      Nat.card {B : Matrix (Fin (n+2)) (Fin 3) (Fin 2) // totals n (arrayEquiv n B).1 = s.val} := by
    exact (Nat.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype
      (fun B => totals n (arrayEquiv n B).1) (traceWord_valid n)).symm).trans (Nat.card_sigma)
  have hw : Nat.card {w : (Fin n → Fin 3 → Fin 2) // WordValid n w} =
      ∑ s : {s : Fin n → Fin 4 // (List.ofFn s).IsChain (· ≠ ·)},
        Nat.card {w : (Fin n → Fin 3 → Fin 2) // totals n w = s.val} := by
    exact (Nat.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype
      (totals n) (totals_valid n)).symm).trans (Nat.card_sigma)
  rw [ha,hw,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [array_fiber, word_fiber]

end D5.S3.Combinatorics.TraceArrays.HardinA185858

namespace D5.S3.Combinatorics.TraceArrays.HardinA185858
open scoped BigOperators

private noncomputable def suffixWeight (n s : ℕ) : ℕ := by
  classical
  exact ∑ w : (Fin n → Fin 3 → Fin 2), if (s :: (List.ofFn w).map hammingNorm).IsChain (· ≠ ·) then 1 else 0

private theorem suffix_zero (s : ℕ) : suffixWeight 0 s = 1 := by
  exact Eq.symm (Nat.eq_of_beq_eq_true rfl)

private theorem suffix_succ (n s : ℕ) :
    suffixWeight (n+1) s = ∑ t : (Fin 3 → Fin 2), if s ≠ hammingNorm t then suffixWeight n (hammingNorm t) else 0 := by
  classical
  unfold suffixWeight
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => (Fin 3 → Fin 2))).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_cons,
    List.map_cons, List.isChain_cons_cons]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : s ≠ hammingNorm t <;> simp [h]

private theorem triple_univ : (Finset.univ : Finset (Fin 3 → Fin 2)) =
    {![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1],
     ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1]} := by
  exact ((Finset.compl_eq_empty_iff
    ({![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1],
      ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1]} : Finset (Fin 3 → Fin 2))).mp rfl).symm

private theorem sum_triple (f : ℕ → ℕ) :
    (∑ t : (Fin 3 → Fin 2), f (hammingNorm t)) = f 0 + 3*f 1 + 3*f 2 + f 3 := by
  rw [triple_univ]
  simp [hammingNorm, Fin.card_filter_univ_succ]
  omega

private theorem word_card (n : ℕ) :
    Nat.card {w : (Fin (n+1) → Fin 3 → Fin 2) // WordValid (n+1) w} =
      suffixWeight n 0 + 3*suffixWeight n 1 + 3*suffixWeight n 2 + suffixWeight n 3 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  simp only [WordValid]
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => (Fin 3 → Fin 2))).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_cons]
  have hc (t : (Fin 3 → Fin 2)) (w : (Fin n → Fin 3 → Fin 2)) :
      (t :: List.ofFn w).IsChain (fun a b => hammingNorm a ≠ hammingNorm b) ↔
      (hammingNorm t :: (List.ofFn w).map hammingNorm).IsChain (· ≠ ·) := by
    exact (List.isChain_map hammingNorm).symm
  simp_rw [hc]
  exact sum_triple (suffixWeight n)

private theorem suffix_equations (n : ℕ) :
    suffixWeight (n+1) 0 = 3*suffixWeight n 1 + 3*suffixWeight n 2 + suffixWeight n 3 ∧
    suffixWeight (n+1) 1 = suffixWeight n 0 + 3*suffixWeight n 2 + suffixWeight n 3 ∧
    suffixWeight (n+1) 2 = suffixWeight n 0 + 3*suffixWeight n 1 + suffixWeight n 3 ∧
    suffixWeight (n+1) 3 = suffixWeight n 0 + 3*suffixWeight n 1 + 3*suffixWeight n 2 := by
  simp only [suffix_succ]
  have h (s : ℕ) : (∑ t : (Fin 3 → Fin 2), if s ≠ hammingNorm t then suffixWeight n (hammingNorm t) else 0) =
      (if s ≠ 0 then suffixWeight n 0 else 0) +
      3*(if s ≠ 1 then suffixWeight n 1 else 0) +
      3*(if s ≠ 2 then suffixWeight n 2 else 0) +
      (if s ≠ 3 then suffixWeight n 3 else 0) :=
    sum_triple (fun j => if s ≠ j then suffixWeight n j else 0)
  rw [h, h, h, h]
  simp

private theorem suffix_symmetry (n : ℕ) :
    suffixWeight n 0 = suffixWeight n 3 ∧ suffixWeight n 1 = suffixWeight n 2 := by
  induction n with
  | zero => simp [suffix_zero]
  | succ n ih =>
    obtain ⟨h0,h1,h2,h3⟩ := suffix_equations n
    constructor <;> omega

private theorem word_recurrence (n : ℕ) :
    Nat.card {w : (Fin (n+3) → Fin 3 → Fin 2) // WordValid (n+3) w} =
      4*Nat.card {w : (Fin (n+2) → Fin 3 → Fin 2) // WordValid (n+2) w} +
      9*Nat.card {w : (Fin (n+1) → Fin 3 → Fin 2) // WordValid (n+1) w} := by
  rw [word_card, word_card, word_card]
  obtain ⟨h0,h1,h2,h3⟩ := suffix_equations n
  obtain ⟨g0,g1,g2,g3⟩ := suffix_equations (n+1)
  change suffixWeight (n+2) 0 =
    3*suffixWeight (n+1) 1 + 3*suffixWeight (n+1) 2 + suffixWeight (n+1) 3 at g0
  change suffixWeight (n+2) 1 =
    suffixWeight (n+1) 0 + 3*suffixWeight (n+1) 2 + suffixWeight (n+1) 3 at g1
  change suffixWeight (n+2) 2 =
    suffixWeight (n+1) 0 + 3*suffixWeight (n+1) 1 + suffixWeight (n+1) 3 at g2
  change suffixWeight (n+2) 3 =
    suffixWeight (n+1) 0 + 3*suffixWeight (n+1) 1 + 3*suffixWeight (n+1) 2 at g3
  rw [g0,g1,g2,g3]
  simp only [h0,h1,h2,h3]
  ring

private theorem count_recurrence (n : ℕ) :
    count (n+3) = 4*count (n+2) + 9*count (n+1) := by
  rw [count_words, count_words, count_words, word_recurrence]
  omega

private theorem a_recurrence (n : ℕ) : a (n+3) = 4*a (n+2) + 9*a (n+1) := by
  unfold a
  rw [count_recurrence]
  push_cast
  ring

private theorem count_normalized (n : ℕ) :
    count (n+1) = 128 * (suffixWeight n 0 + 3*suffixWeight n 1) := by
  rw [count_words,word_card]
  obtain ⟨h0,h1⟩ := suffix_symmetry n
  omega

private theorem a_initial : a 1 = 4 ∧ a 2 = 22 := by
  have h0 := (suffix_equations 0).1
  have h1 := (suffix_equations 0).2.1
  norm_num [suffix_zero] at h0 h1
  unfold a
  rw [count_normalized, count_normalized]
  norm_num [suffix_zero, h0, h1]

end D5.S3.Combinatorics.TraceArrays.HardinA185858
namespace D5.S3.Combinatorics.TraceArrays.HardinA185858

private theorem series_formula
    (h1 : a 1 = 4) (h2 : a 2 = 22)
    (hr : ∀ n, a (n+3) = 4*a (n+2) + 9*a (n+1)) :
    generatingSeries =
      (2 * PowerSeries.X * (2 + 3 * PowerSeries.X)) *
        (1 - 4 * PowerSeries.X - 9 * PowerSeries.X ^ 2)⁻¹ := by
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp)).mpr
  have he : generatingSeries * (1 - 4 * PowerSeries.X - 9 * PowerSeries.X ^ 2) =
      generatingSeries - 4*(PowerSeries.X*generatingSeries) -
        9*(PowerSeries.X*(PowerSeries.X*generatingSeries)) := by ring
  rw [he, show (2 * PowerSeries.X * (2 + 3 * PowerSeries.X) : PowerSeries ℚ) =
    4*PowerSeries.X + 6*(PowerSeries.X*PowerSeries.X) by ring]
  ext k
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ ∃ n, k = n+3 := by
    by_cases h0 : k = 0
    · exact Or.inl h0
    by_cases h1 : k = 1
    · exact Or.inr (Or.inl h1)
    by_cases h2 : k = 2
    · exact Or.inr (Or.inr (Or.inl h2))
    exact Or.inr (Or.inr (Or.inr ⟨k-3, by omega⟩))
  obtain rfl | rfl | rfl | ⟨n,rfl⟩ := hk
  · simp [generatingSeries]
  · simp [generatingSeries, PowerSeries.coeff_succ_X_mul, h1]
  · norm_num [generatingSeries, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X, h1, h2]
  · simp only [map_sub, map_add, PowerSeries.coeff_ofNat_mul,
      PowerSeries.coeff_succ_X_mul]
    simp [generatingSeries, PowerSeries.coeff_X]
    linarith [hr n]

private noncomputable def radical (n : ℕ) : ℝ :=
  (((2 - Real.sqrt 13) ^ n * (-4 + Real.sqrt 13) +
    (2 + Real.sqrt 13) ^ n * (4 + Real.sqrt 13)) / (3 * Real.sqrt 13))

private theorem radical_recurrence (n : ℕ) :
    radical (n+3) = 4*radical (n+2) + 9*radical (n+1) := by
  have hs : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hm : (2 - Real.sqrt 13)^2 = 4*(2 - Real.sqrt 13) + 9 := by nlinarith
  have hp : (2 + Real.sqrt 13)^2 = 4*(2 + Real.sqrt 13) + 9 := by nlinarith
  have power (r : ℝ) (h : r^2 = 4*r+9) :
      r^(n+3) = 4*r^(n+2)+9*r^(n+1) := by
    let E : LinearRecurrence ℝ := ⟨2, ![9,4]⟩
    have hr : E.charPoly.IsRoot r := by
      simp only [LinearRecurrence.charPoly, E, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
        Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_monomial, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
        mul_one, one_mul]
      linarith [h]
    have hs := (E.geom_sol_iff_root_charPoly r).2 hr (n+1)
    simpa [E, Fin.sum_univ_two, Nat.add_assoc, add_comm, add_left_comm] using hs
  unfold radical
  rw [power _ hm, power _ hp]
  ring

private theorem radical_initial : radical 1 = 4 ∧ radical 2 = 22 := by
  have hs : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 13 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<13)).ne'
  constructor <;> unfold radical <;> field_simp [hn] <;> nlinarith

private theorem closed_formula
    (h1 : a 1 = 4) (h2 : a 2 = 22)
    (hr : ∀ n, a (n+3) = 4*a (n+2) + 9*a (n+1)) :
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = radical n := by
  let E : LinearRecurrence ℝ := ⟨2, ![9,4]⟩
  have hu : E.IsSolution (fun n => (a (n+1) : ℝ)) := by
    intro n
    simp only [E, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have hc : (a (n+3) : ℝ) = 4*(a (n+2) : ℝ)+9*(a (n+1) : ℝ) := by
      exact_mod_cast hr n
    simpa [Nat.add_assoc] using hc.trans (add_comm _ _)
  have hv : E.IsSolution (fun n => radical (n+1)) := by
    intro n
    simp only [E, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simpa [Nat.add_assoc] using (radical_recurrence n).trans (add_comm _ _)
  have he : (fun n => (a (n+1) : ℝ)) = (fun n => radical (n+1)) := by
    apply (E.eq_iff_eqOn_range_order _ _ hu hv).2
    intro n hn
    have hlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · simpa [h1] using radical_initial.1.symm
    · simpa [h2] using radical_initial.2.symm
  intro n hn
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm] using congrFun he m

end D5.S3.Combinatorics.TraceArrays.HardinA185858

namespace D5.S3.Combinatorics.TraceArrays.HardinA185858
theorem result : claim := by
  exact ⟨series_formula a_initial.1 a_initial.2 a_recurrence,
    closed_formula a_initial.1 a_initial.2 a_recurrence⟩
end D5.S3.Combinatorics.TraceArrays.HardinA185858
