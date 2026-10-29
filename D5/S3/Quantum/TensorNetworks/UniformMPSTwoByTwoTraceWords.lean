/- GID: D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoTraceWords
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoTraceWords
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Trace words and invariants of pairs of two-by-two complex matrices. -/

import D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Polynomial.Basic
import D5.S0.Observation.MatrixTracePowerSum
import Mathlib.Tactic.Module

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords

open scoped BigOperators Matrix
open UniformMPSExpectedDimensionRefutation (traceWord uMPS)

noncomputable section

private abbrev parameters := Fin 2 → Matrix (Fin 2) (Fin 2) ℂ

private def degree (e : Fin 5 → ℕ) : ℕ :=
  e 0 + e 1 + 2 * e 2 + 2 * e 3 + 2 * e 4

private def invariants (p : parameters) : Fin 5 → ℂ :=
  ![(p 0).trace, (p 1).trace, (p 0).det, (p 1).det, (p 0 * p 1).trace]

private def mon (e : Fin 5 → ℕ) (p : parameters) : ℂ :=
  ∏ j : Fin 5, invariants p j ^ e j

private def graded (k : ℤ) : Submodule ℂ (parameters → ℂ) :=
  Submodule.span ℂ {f | ∃ e : Fin 5 → ℕ, (degree e : ℤ) = k ∧ f = mon e}

private def commutator (p : parameters) : Matrix (Fin 2) (Fin 2) ℂ :=
  p 0 * p 1 - p 1 * p 0

private def delta (p : parameters) : ℂ :=
  invariants p 4 ^ 2 - invariants p 0 * invariants p 1 * invariants p 4 +
    invariants p 0 ^ 2 * invariants p 3 + invariants p 1 ^ 2 * invariants p 2 -
    4 * invariants p 2 * invariants p 3

private def deltaMap : (parameters → ℂ) →ₗ[ℂ] (parameters → ℂ) where
  toFun f p := delta p * f p
  map_add' f g := by ext p; exact mul_add _ _ _
  map_smul' c f := by ext p; exact mul_left_comm _ _ _

private def word (l : List (Fin 2)) (p : parameters) : Matrix (Fin 2) (Fin 2) ℂ :=
  (l.map p).prod

private def coordinates (n : ℕ) : Submodule ℂ (parameters → ℂ) :=
  Submodule.span ℂ (Set.range fun i : Fin n → Fin 2 => fun p => traceWord 2 2 n p i)

private def ordered (n : ℕ) (a : Fin (n + 1)) (p : parameters) : ℂ :=
  (p 0 ^ a.val * p 1 ^ (n - a.val)).trace

private abbrev extraIndex (n : ℕ) :=
  {e : Fin 5 → Fin (n + 1) // degree (fun j => (e j).val) + 4 = n}

private abbrev normalIndex (n : ℕ) := Fin (n + 1) ⊕ extraIndex n

private def normalFamily (n : ℕ) : normalIndex n → parameters → ℂ :=
  Sum.elim (ordered n) (fun e p => delta p * mon (fun j => (e.val j).val) p)

private lemma mon_add (e f : Fin 5 → ℕ) : mon (e + f) = mon e * mon f := by
  funext p
  change (∏ j : Fin 5, invariants p j ^ (e j + f j)) =
    (∏ j : Fin 5, invariants p j ^ e j) * ∏ j : Fin 5, invariants p j ^ f j
  simp only [pow_add, Finset.prod_mul_distrib]

private lemma degree_add (e f : Fin 5 → ℕ) : degree (e + f) = degree e + degree f := by
  change (e 0 + f 0) + (e 1 + f 1) + 2 * (e 2 + f 2) + 2 * (e 3 + f 3) +
    2 * (e 4 + f 4) =
    (e 0 + e 1 + 2 * e 2 + 2 * e 3 + 2 * e 4) +
    (f 0 + f 1 + 2 * f 2 + 2 * f 3 + 2 * f 4)
  omega

private lemma mon_single (j : Fin 5) (k : ℕ) :
    mon (Pi.single j k) = fun p => invariants p j ^ k := by
  classical
  funext p
  change (∏ a : Fin 5, invariants p a ^ (Pi.single j k a)) = invariants p j ^ k
  rw [Finset.prod_eq_single j]
  · simp only [Pi.single_eq_same]
  · intro b _ hb
    simp only [Pi.single_eq_of_ne hb, pow_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]

private lemma degree_single (j : Fin 5) :
    degree (Pi.single j 1) = if j.val < 2 then 1 else 2 := by
  fin_cases j <;> norm_num [degree, Pi.single_apply]

private lemma graded_mul {i j : ℤ} {f g : parameters → ℂ}
    (hf : f ∈ graded i) (hg : g ∈ graded j) : f * g ∈ graded (i + j) := by
  change f ∈ Submodule.span ℂ _ at hf
  change g ∈ Submodule.span ℂ _ at hg
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨e, he, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, ha, rfl⟩ := hg
      rw [← mon_add]
      exact Submodule.subset_span ⟨e + a, by rw [degree_add, Nat.cast_add, he, ha], rfl⟩
    | zero => simpa only [mul_zero] using (graded (i + j)).zero_mem
    | add g h _ _ hg hh =>
      rw [mul_add]
      exact (graded (i + j)).add_mem hg hh
    | smul c g _ hg =>
      rw [mul_smul_comm]
      exact (graded (i + j)).smul_mem c hg
  | zero => simpa only [zero_mul] using (graded (i + j)).zero_mem
  | add f h _ _ hf hh =>
    rw [add_mul]
    exact (graded (i + j)).add_mem hf hh
  | smul c f _ hf =>
    rw [smul_mul_assoc]
    exact (graded (i + j)).smul_mem c hf

private lemma graded_one : (1 : parameters → ℂ) ∈ graded 0 := by
  refine Submodule.subset_span ⟨0, rfl, ?_⟩
  funext p
  change 1 = ∏ j : Fin 5, invariants p j ^ (0 : ℕ)
  simp only [pow_zero, Finset.prod_const_one]

private lemma mon_zero (p : parameters) : mon 0 p = 1 := by
  change (∏ j : Fin 5, invariants p j ^ (0 : ℕ)) = 1
  simp only [pow_zero, Finset.prod_const_one]

private lemma invariant_mem (j : Fin 5) :
    (fun p => invariants p j) ∈ graded (if j.val < 2 then 1 else 2) := by
  classical
  refine Submodule.subset_span ⟨Pi.single j 1, ?_, ?_⟩
  · rw [degree_single]
    split_ifs <;> rfl
  · rw [mon_single]
    simp only [pow_one]

private lemma cayley_hamilton (x : Matrix (Fin 2) (Fin 2) ℂ) :
    x * x = x.trace • x - x.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simpa only [Nat.zero_add, pow_zero, pow_one, pow_two] using
    D5.S0.Observation.MatrixTracePowerSum.pow_add_two x 0

private lemma polarized_cayley_hamilton (x y : Matrix (Fin 2) (Fin 2) ℂ) :
    y * x = x.trace • y + y.trace • x +
      ((x * y).trace - x.trace * y.trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - x * y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.trace_fin_two, smul_eq_mul,
      Fin.mk_zero, Fin.mk_one, Fin.zero_ne_one, Fin.ext_iff, Fin.val_zero, Fin.val_one,
      Nat.one_ne_zero, Nat.zero_ne_one, ↓reduceIte] <;> ring

private lemma sandwich (x y : Matrix (Fin 2) (Fin 2) ℂ) :
    y * x * y = (x * y).trace • y + y.det • x -
      (x.trace * y.det) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.trace_fin_two, Matrix.det_fin_two,
      smul_eq_mul, Fin.mk_zero, Fin.mk_one, Fin.zero_ne_one, Fin.ext_iff,
      Fin.val_zero, Fin.val_one, Nat.one_ne_zero, Nat.zero_ne_one, ↓reduceIte] <;> ring

private lemma reduction_left_x (x y : Matrix (Fin 2) (Fin 2) ℂ) (a b c d : ℂ) :
    x * (a • 1 + b • x + c • y + d • (x * y)) =
      (-(x.det * b)) • 1 + (a + x.trace * b) • x + (-(x.det * d)) • y +
        (c + x.trace * d) • (x * y) := by
  simp only [mul_add, mul_smul_comm, mul_one, ← Matrix.mul_assoc, cayley_hamilton,
    sub_mul, smul_mul_assoc, one_mul]
  module

private lemma reduction_left_y (x y : Matrix (Fin 2) (Fin 2) ℂ) (a b c d : ℂ) :
    y * (a • 1 + b • x + c • y + d • (x * y)) =
      (((x * y).trace - x.trace * y.trace) * b - y.det * c -
        x.trace * y.det * d) • 1 + (y.trace * b + y.det * d) • x +
      (a + x.trace * b + y.trace * c + (x * y).trace * d) • y + (-b) • (x * y) := by
  have hxy : y * (x * y) = (x * y).trace • y + y.det • x -
      (x.trace * y.det) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simpa only [Matrix.mul_assoc] using sandwich x y
  simp only [mul_add, mul_smul_comm, mul_one, hxy, polarized_cayley_hamilton x y,
    cayley_hamilton y]
  module

private lemma word_reduction (l : List (Fin 2)) :
    ∃ r : Fin 4 → parameters → ℂ,
      r 0 ∈ graded l.length ∧ r 1 ∈ graded ((l.length : ℤ) - 1) ∧
      r 2 ∈ graded ((l.length : ℤ) - 1) ∧ r 3 ∈ graded ((l.length : ℤ) - 2) ∧
      ∀ p, word l p = r 0 p • 1 + r 1 p • p 0 + r 2 p • p 1 +
        r 3 p • (p 0 * p 1) := by
  induction l with
  | nil =>
    refine ⟨(![1, 0, 0, 0] : Fin 4 → parameters → ℂ), ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, List.length_nil,
        Nat.cast_zero, zero_sub]
    · exact graded_one
    · exact (graded (-1)).zero_mem
    · exact (graded (-1)).zero_mem
    · exact (graded (-2)).zero_mem
    · intro p
      change 1 = (1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (0 : ℂ) • p 0 + (0 : ℂ) • p 1 + (0 : ℂ) • (p 0 * p 1)
      simp only [one_smul, zero_smul, add_zero]
  | cons a l ih =>
    obtain ⟨r, hr0, hr1, hr2, hr3, hr⟩ := ih
    have hs : (fun p => invariants p 0) ∈ graded 1 := invariant_mem 0
    have ht : (fun p => invariants p 1) ∈ graded 1 := invariant_mem 1
    have hu : (fun p => invariants p 2) ∈ graded 2 := invariant_mem 2
    have hv : (fun p => invariants p 3) ∈ graded 2 := invariant_mem 3
    have hw : (fun p => invariants p 4) ∈ graded 2 := invariant_mem 4
    have hm {i j k : ℤ} {f g : parameters → ℂ}
        (hf : f ∈ graded i) (hg : g ∈ graded j) (h : i + j = k) :
        f * g ∈ graded k := h ▸ graded_mul hf hg
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [show (l.length : ℤ) + 1 - 2 = (l.length : ℤ) - 1 by omega]
    fin_cases a
    · refine ⟨![-((fun p => invariants p 2) * r 1),
        r 0 + (fun p => invariants p 0) * r 1,
        -((fun p => invariants p 2) * r 3),
        r 2 + (fun p => invariants p 0) * r 3], ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      · exact (graded _).neg_mem (hm hu hr1 (by omega))
      · exact (graded _).add_mem hr0 (hm hs hr1 (by omega))
      · exact (graded _).neg_mem (hm hu hr3 (by omega))
      · exact (graded _).add_mem hr2 (hm hs hr3 (by omega))
      · intro p
        change p 0 * word l p = _
        rw [hr p]
        exact reduction_left_x (p 0) (p 1) (r 0 p) (r 1 p) (r 2 p) (r 3 p)
    · have hws : ((fun p => invariants p 4) -
          (fun p => invariants p 0) * (fun p => invariants p 1)) ∈ graded 2 :=
        (graded _).sub_mem hw (hm hs ht (by omega))
      have hsv : (fun p => invariants p 0) * (fun p => invariants p 3) ∈ graded 3 :=
        hm hs hv (by omega)
      refine ⟨![((fun p => invariants p 4) -
          (fun p => invariants p 0) * (fun p => invariants p 1)) * r 1 -
          (fun p => invariants p 3) * r 2 -
          ((fun p => invariants p 0) * (fun p => invariants p 3)) * r 3,
        (fun p => invariants p 1) * r 1 + (fun p => invariants p 3) * r 3,
        r 0 + (fun p => invariants p 0) * r 1 + (fun p => invariants p 1) * r 2 +
          (fun p => invariants p 4) * r 3, -r 1], ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      · exact (graded _).sub_mem ((graded _).sub_mem (hm hws hr1 (by omega))
          (hm hv hr2 (by omega))) (hm hsv hr3 (by omega))
      · exact (graded _).add_mem (hm ht hr1 (by omega)) (hm hv hr3 (by omega))
      · exact (graded _).add_mem ((graded _).add_mem ((graded _).add_mem hr0
          (hm hs hr1 (by omega))) (hm ht hr2 (by omega))) (hm hw hr3 (by omega))
      · exact (graded _).neg_mem hr1
      · intro p
        change p 1 * word l p = _
        rw [hr p]
        exact reduction_left_y (p 0) (p 1) (r 0 p) (r 1 p) (r 2 p) (r 3 p)

private lemma commutator_traces (p : parameters) :
    (commutator p).trace = 0 ∧ (p 0 * commutator p).trace = 0 ∧
      (p 1 * commutator p).trace = 0 ∧ (p 0 * p 1 * commutator p).trace = delta p := by
  have h0 : (commutator p).trace = 0 := by
    change (p 0 * p 1 - p 1 * p 0).trace = 0
    rw [Matrix.trace_sub, Matrix.trace_mul_comm (p 0) (p 1), sub_self]
  have hx : (p 0 * commutator p).trace = 0 := by
    change (p 0 * (p 0 * p 1 - p 1 * p 0)).trace = 0
    rw [mul_sub, Matrix.trace_sub, Matrix.trace_mul_cycle' (p 0) (p 1) (p 0), sub_self]
  have hy : (p 1 * commutator p).trace = 0 := by
    change (p 1 * (p 0 * p 1 - p 1 * p 0)).trace = 0
    rw [mul_sub, Matrix.trace_sub, Matrix.trace_mul_cycle' (p 1) (p 0) (p 1), sub_self]
  refine ⟨h0, hx, hy, ?_⟩
  change (p 0 * p 1 * (p 0 * p 1 - p 1 * p 0)).trace =
    (p 0 * p 1).trace ^ 2 - (p 0).trace * (p 1).trace * (p 0 * p 1).trace +
      (p 0).trace ^ 2 * (p 1).det + (p 1).trace ^ 2 * (p 0).det -
      4 * (p 0).det * (p 1).det
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.sub_apply,
    Fin.sum_univ_two, Matrix.det_fin_two]
  ring

private lemma trace_word_commutator (l : List (Fin 2)) :
    (fun p => (word l p * commutator p).trace) ∈
      (graded ((l.length : ℤ) - 2)).map deltaMap := by
  obtain ⟨r, _, _, _, hr3, hr⟩ := word_reduction l
  refine ⟨r 3, hr3, ?_⟩
  funext p
  change delta p * r 3 p = (word l p * commutator p).trace
  rw [hr p]
  obtain ⟨h0, hx, hy, hxy⟩ := commutator_traces p
  simp only [add_mul, smul_mul_assoc, one_mul, Matrix.trace_add, Matrix.trace_smul,
    h0, hx, hy, hxy, smul_eq_mul, mul_zero, zero_add]
  exact mul_comm _ _

private lemma word_append (a b : List (Fin 2)) (p : parameters) :
    word (a ++ b) p = word a p * word b p := by
  change ((a ++ b).map p).prod = (a.map p).prod * (b.map p).prod
  rw [List.map_append, List.prod_append]

private lemma word_cons (a : Fin 2) (l : List (Fin 2)) (p : parameters) :
    word (a :: l) p = p a * word l p := rfl

private lemma word_nil (p : parameters) : word [] p = 1 := rfl

private lemma word_replicate (n : ℕ) (a : Fin 2) (p : parameters) :
    word (List.replicate n a) p = p a ^ n := by
  change ((List.replicate n a).map p).prod = p a ^ n
  rw [List.map_replicate, List.prod_replicate]

private lemma word_trace_mem (l : List (Fin 2)) :
    (fun p => (word l p).trace) ∈ coordinates l.length := by
  apply Submodule.subset_span
  refine ⟨l.get, ?_⟩
  funext p
  change ((List.ofFn (p ∘ l.get)).prod).trace = ((l.map p).prod).trace
  rw [← List.map_ofFn, List.ofFn_get]

private lemma trace_swap_identity (a b x y : Matrix (Fin 2) (Fin 2) ℂ) :
    (a * x * y * b).trace - (a * y * x * b).trace =
      (b * a * (x * y - y * x)).trace := by
  rw [mul_sub, Matrix.trace_sub, Matrix.trace_mul_cycle (a * x) y b,
    Matrix.trace_mul_cycle (a * y) x b]
  simp only [Matrix.mul_assoc]

private lemma trace_swap (a b : List (Fin 2)) :
    (fun p => (word (a ++ 0 :: 1 :: b) p).trace -
      (word (a ++ 1 :: 0 :: b) p).trace) =
    (fun p => (word (b ++ a) p * commutator p).trace) := by
  funext p
  change _ = (word (b ++ a) p * (p 0 * p 1 - p 1 * p 0)).trace
  simp only [word_append, word_cons, ← Matrix.mul_assoc]
  exact trace_swap_identity (word a p) (word b p) (p 0) (p 1)

private lemma trace_adjacent_mem (a b : List (Fin 2)) (x y : Fin 2) :
    (fun p => (word (a ++ x :: y :: b) p).trace -
      (word (a ++ y :: x :: b) p).trace) ∈
      (graded (((a ++ x :: y :: b).length : ℤ) - 4)).map deltaMap := by
  have h : (fun p => (word (b ++ a) p * commutator p).trace) ∈
      (graded (((a ++ x :: y :: b).length : ℤ) - 4)).map deltaMap := by
    have hd : (((b ++ a).length : ℤ) - 2) = (((a ++ x :: y :: b).length : ℤ) - 4) := by
      simp only [List.length_append, List.length_cons, Nat.cast_add, Nat.cast_one]
      omega
    rw [← hd]
    exact trace_word_commutator (b ++ a)
  fin_cases x <;> fin_cases y <;> simp only [Fin.mk_zero, Fin.mk_one] at *
  · simpa only [sub_self, Pi.zero_def] using
      ((graded (((a ++ (0 : Fin 2) :: 0 :: b).length : ℤ) - 4)).map deltaMap).zero_mem
  · rw [trace_swap]
    exact h
  · have heq : (fun p => (word (a ++ (1 : Fin 2) :: 0 :: b) p).trace -
        (word (a ++ 0 :: 1 :: b) p).trace) =
        -(fun p => (word (b ++ a) p * commutator p).trace) := by
      rw [← trace_swap]
      funext p
      change _ - _ = -(_ - _)
      ring
    rw [heq]
    exact (Submodule.map deltaMap _).neg_mem h
  · simpa only [sub_self, Pi.zero_def] using
      ((graded (((a ++ (1 : Fin 2) :: 1 :: b).length : ℤ) - 4)).map deltaMap).zero_mem

private lemma trace_perm_mem {l r : List (Fin 2)} (h : l.Perm r) (a : List (Fin 2)) :
    (fun p => (word (a ++ l) p).trace - (word (a ++ r) p).trace) ∈
      (graded (((a ++ l).length : ℤ) - 4)).map deltaMap := by
  induction h generalizing a with
  | nil =>
    refine ⟨(0 : parameters → ℂ), (graded _).zero_mem, ?_⟩
    funext p
    change delta p * 0 = (word (a ++ []) p).trace - (word (a ++ []) p).trace
    rw [mul_zero, sub_self]
  | cons x h ih =>
    simpa only [List.append_assoc, List.singleton_append] using ih (a ++ [x])
  | swap x y l => exact trace_adjacent_mem a l y x
  | @trans l r t h1 h2 ih1 ih2 =>
    have ht : (fun p => (word (a ++ r) p).trace - (word (a ++ t) p).trace) ∈
        (graded (((a ++ l).length : ℤ) - 4)).map deltaMap := by
      simpa only [List.length_append, h1.length_eq] using ih2 a
    have heq : (fun p : parameters => (word (a ++ l) p).trace -
        (word (a ++ t) p).trace) =
        (fun p => (word (a ++ l) p).trace - (word (a ++ r) p).trace) +
        (fun p => (word (a ++ r) p).trace - (word (a ++ t) p).trace) := by
      funext p
      change (word (a ++ l) p).trace - (word (a ++ t) p).trace =
        ((word (a ++ l) p).trace - (word (a ++ r) p).trace) +
        ((word (a ++ r) p).trace - (word (a ++ t) p).trace)
      ring
    exact (congrArg (fun f : parameters → ℂ => f ∈
      (graded (((a ++ l).length : ℤ) - 4)).map deltaMap) heq).mpr
        (((graded (((a ++ l).length : ℤ) - 4)).map deltaMap).add_mem (ih1 a) ht)

private lemma binary_count (l : List (Fin 2)) : l.count 0 + l.count 1 = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    fin_cases x <;> simp_all <;> omega

private lemma sorted_perm (l : List (Fin 2)) :
    l.Perm (List.replicate (l.count 0) 0 ++ List.replicate (l.count 1) 1) := by
  apply List.perm_iff_count.mpr
  intro x
  fin_cases x <;> simp [List.count_replicate]

private lemma coordinates_upper (n : ℕ) :
    coordinates n ≤ Submodule.span ℂ (Set.range (ordered n)) ⊔
      (graded ((n : ℤ) - 4)).map deltaMap := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  let l := List.ofFn i
  let a : Fin (n + 1) := ⟨l.count 0, by
    have h := List.count_le_length (a := (0 : Fin 2)) (l := l)
    have hl : l.length = n := List.length_ofFn
    omega⟩
  have hp := trace_perm_mem (sorted_perm l) []
  have hl : l.length = n := List.length_ofFn
  have hc : l.count 1 = n - l.count 0 := by have h := binary_count l; omega
  have ho : (fun p => (word (List.replicate (l.count 0) 0 ++
      List.replicate (l.count 1) 1) p).trace) = ordered n a := by
    funext p
    change _ = (p 0 ^ l.count 0 * p 1 ^ (n - l.count 0)).trace
    rw [word_append, word_replicate, word_replicate, hc]
  have hi : (fun p => (word l p).trace) = (fun p => traceWord 2 2 n p i) := by
    funext p
    change ((List.map p (List.ofFn i)).prod).trace =
      ((List.ofFn fun k => p (i k)).prod).trace
    rw [List.map_ofFn]
    rfl
  simp only [List.nil_append, hl] at hp
  have heq : (fun p => traceWord 2 2 n p i - ordered n a p) =
      (fun p => (word l p).trace -
        (word (List.replicate (l.count 0) 0 ++ List.replicate (l.count 1) 1) p).trace) := by
    funext p
    rw [← congrFun hi p, ← congrFun ho p]
  rw [← heq] at hp
  have hs : ordered n a ∈ Submodule.span ℂ (Set.range (ordered n)) :=
    Submodule.subset_span ⟨a, rfl⟩
  have ht : (fun p => traceWord 2 2 n p i - ordered n a p) ∈
      Submodule.span ℂ (Set.range (ordered n)) ⊔ (graded ((n : ℤ) - 4)).map deltaMap :=
    Submodule.mem_sup_right hp
  have hu : ordered n a ∈ Submodule.span ℂ (Set.range (ordered n)) ⊔
      (graded ((n : ℤ) - 4)).map deltaMap := Submodule.mem_sup_left hs
  have hfun : (fun p => traceWord 2 2 n p i) =
      (fun p => traceWord 2 2 n p i - ordered n a p) + ordered n a := by
    funext p
    change traceWord 2 2 n p i = (traceWord 2 2 n p i - ordered n a p) + ordered n a p
    ring
  change (fun p => traceWord 2 2 n p i) ∈ _
  rw [hfun]
  exact (Submodule.span ℂ (Set.range (ordered n)) ⊔
    (graded ((n : ℤ) - 4)).map deltaMap).add_mem ht hu

private def combinationEval (q : List (Fin 2) →₀ ℂ) (p : parameters) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  q.sum fun l c => c • word l p

private def pureWords (n : ℕ) (q : List (Fin 2) →₀ ℂ) : Prop :=
  ∀ l ∈ q.support, l.length = n

private def wrap (a b : List (Fin 2)) (q : List (Fin 2) →₀ ℂ) :
    List (Fin 2) →₀ ℂ := q.mapDomain fun l => a ++ l ++ b

private lemma pure_add {n : ℕ} {q r : List (Fin 2) →₀ ℂ}
    (hq : pureWords n q) (hr : pureWords n r) : pureWords n (q + r) := by
  intro l hl
  rcases Finset.mem_union.mp (Finsupp.support_add hl) with hl | hl
  · exact hq l hl
  · exact hr l hl

private lemma pure_single (l : List (Fin 2)) (c : ℂ) :
    pureWords l.length (Finsupp.single l c) := by
  intro r hr
  have heq : r = l := Finset.mem_singleton.mp (Finsupp.support_single_subset hr)
  rw [heq]

private lemma pure_wrap {n : ℕ} {q : List (Fin 2) →₀ ℂ} (hq : pureWords n q)
    (a b : List (Fin 2)) : pureWords (a.length + n + b.length) (wrap a b q) := by
  intro l hl
  change l ∈ (q.mapDomain fun l => a ++ l ++ b).support at hl
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hl)
  simp only [List.length_append, hq r hr]

private lemma combinationEval_add (q r : List (Fin 2) →₀ ℂ) (p : parameters) :
    combinationEval (q + r) p = combinationEval q p + combinationEval r p := by
  change (q + r).sum (fun l c => c • word l p) =
    q.sum (fun l c => c • word l p) + r.sum (fun l c => c • word l p)
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

private lemma combinationEval_single (l : List (Fin 2)) (c : ℂ) (p : parameters) :
    combinationEval (Finsupp.single l c) p = c • word l p := by
  change (Finsupp.single l c).sum (fun l c => c • word l p) = c • word l p
  exact Finsupp.sum_single_index (zero_smul ℂ (word l p))

private lemma wrap_eval (a b : List (Fin 2)) (q : List (Fin 2) →₀ ℂ) (p : parameters) :
    combinationEval (wrap a b q) p = word a p * combinationEval q p * word b p := by
  change (q.mapDomain fun l => a ++ l ++ b).sum (fun l c => c • word l p) = _
  rw [Finsupp.sum_mapDomain_index (h := fun l (c : ℂ) => c • word l p)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [word_append]
  change (∑ l ∈ q.support, q l • (word a p * word l p * word b p)) =
    word a p * (∑ l ∈ q.support, q l • word l p) * word b p
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]

private def wordOp (j : Fin 5) (q : List (Fin 2) →₀ ℂ) : List (Fin 2) →₀ ℂ :=
  ![wrap [0] [] q + wrap [] [0] q, wrap [1] [] q + wrap [] [1] q,
    wrap [0] [0] q, wrap [1] [1] q, wrap [0, 1] [] q + wrap [] [1, 0] q] j

private lemma wordOp_pure (j : Fin 5) {n : ℕ} {q : List (Fin 2) →₀ ℂ}
    (hq : pureWords n q) :
    pureWords (n + if j.val < 2 then 1 else 2) (wordOp j q) := by
  have hw (a b : List (Fin 2)) := pure_wrap hq a b
  fin_cases j <;>
    simp only [wordOp, Matrix.cons_val_zero, Matrix.cons_val_succ', Matrix.cons_val_zero',
      Fin.isValue, Nat.reduceLT, ↓reduceIte]
  · exact pure_add (by simpa [Nat.add_comm] using hw [0] [])
      (by simpa using hw [] [0])
  · exact pure_add (by simpa [Nat.add_comm] using hw [1] [])
      (by simpa using hw [] [1])
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw [0] [0]
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw [1] [1]
  · exact pure_add (by simpa [Nat.add_comm] using hw [0, 1] [])
      (by simpa using hw [] [1, 0])

private lemma commutator_operations (p : parameters) :
    p 0 * commutator p + commutator p * p 0 = invariants p 0 • commutator p ∧
    p 1 * commutator p + commutator p * p 1 = invariants p 1 • commutator p ∧
    p 0 * commutator p * p 0 = invariants p 2 • commutator p ∧
    p 1 * commutator p * p 1 = invariants p 3 • commutator p ∧
    p 0 * p 1 * commutator p + commutator p * p 1 * p 0 =
      invariants p 4 • commutator p := by
  change
    p 0 * (p 0 * p 1 - p 1 * p 0) + (p 0 * p 1 - p 1 * p 0) * p 0 =
      (p 0).trace • (p 0 * p 1 - p 1 * p 0) ∧
    p 1 * (p 0 * p 1 - p 1 * p 0) + (p 0 * p 1 - p 1 * p 0) * p 1 =
      (p 1).trace • (p 0 * p 1 - p 1 * p 0) ∧
    p 0 * (p 0 * p 1 - p 1 * p 0) * p 0 =
      (p 0).det • (p 0 * p 1 - p 1 * p 0) ∧
    p 1 * (p 0 * p 1 - p 1 * p 0) * p 1 =
      (p 1).det • (p 0 * p 1 - p 1 * p 0) ∧
    p 0 * p 1 * (p 0 * p 1 - p 1 * p 0) +
      (p 0 * p 1 - p 1 * p 0) * p 1 * p 0 =
      (p 0 * p 1).trace • (p 0 * p 1 - p 1 * p 0)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.trace_fin_two, Matrix.det_fin_two, smul_eq_mul,
      Fin.mk_zero, Fin.mk_one] <;> ring

private lemma commutator_square (p : parameters) :
    commutator p * commutator p = delta p • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  change (p 0 * p 1 - p 1 * p 0) * (p 0 * p 1 - p 1 * p 0) =
    ((p 0 * p 1).trace ^ 2 - (p 0).trace * (p 1).trace * (p 0 * p 1).trace +
      (p 0).trace ^ 2 * (p 1).det + (p 1).trace ^ 2 * (p 0).det -
      4 * (p 0).det * (p 1).det) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.trace_fin_two, Matrix.det_fin_two, smul_eq_mul,
      Fin.mk_zero, Fin.mk_one, Fin.ext_iff, Fin.val_zero, Fin.val_one,
      Nat.one_ne_zero, Nat.zero_ne_one, ↓reduceIte] <;> ring

private lemma wordOp_eval (j : Fin 5) (q : List (Fin 2) →₀ ℂ) (f : parameters → ℂ)
    (hq : ∀ p, combinationEval q p = f p • commutator p) (p : parameters) :
    combinationEval (wordOp j q) p = (invariants p j * f p) • commutator p := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := commutator_operations p
  simp only [invariants, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons] at h0 h1 h2 h3 h4
  fin_cases j <;>
    simp only [wordOp, invariants, Matrix.cons_val_zero, Matrix.cons_val_zero',
      Matrix.cons_val_succ', combinationEval_add, wrap_eval, word_cons, word_nil,
      one_mul, mul_one, hq p]
  · simpa only [mul_smul_comm, smul_mul_assoc, ← smul_add, smul_smul, mul_comm] using
      congrArg (fun a => f p • a) h0
  · simpa only [mul_smul_comm, smul_mul_assoc, ← smul_add, smul_smul, mul_comm] using
      congrArg (fun a => f p • a) h1
  · simpa only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm] using
      congrArg (fun a => f p • a) h2
  · simpa only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm] using
      congrArg (fun a => f p • a) h3
  · simpa only [← Matrix.mul_assoc, mul_smul_comm, smul_mul_assoc, ← smul_add,
      smul_smul, mul_comm] using congrArg (fun a => f p • a) h4

private lemma invariant_multiple (e : Fin 5 → ℕ) :
    ∃ q : List (Fin 2) →₀ ℂ,
      (∀ l ∈ q.support, l.length = degree e + 2) ∧
      ∀ p, combinationEval q p = mon e p • commutator p := by
  classical
  let q0 : List (Fin 2) →₀ ℂ := Finsupp.single [0, 1] 1 + Finsupp.single [1, 0] (-1)
  have hq0 : pureWords 2 q0 := pure_add (pure_single [0, 1] 1) (pure_single [1, 0] (-1))
  have hq0eval (p : parameters) : combinationEval q0 p = commutator p := by
    rw [combinationEval_add, combinationEval_single, combinationEval_single]
    simp only [word_cons, word_nil, mul_one, one_smul, neg_one_smul]
    rfl
  suffices ∀ m (f : Fin 5 → ℕ), (∑ j, f j) = m →
      ∃ q : List (Fin 2) →₀ ℂ, pureWords (degree f + 2) q ∧
        ∀ p, combinationEval q p = mon f p • commutator p from this _ e rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro f hf
    by_cases hz : f = 0
    · subst f
      refine ⟨q0, ?_, ?_⟩
      · exact hq0
      · intro p
        rw [mon_zero, one_smul]
        exact hq0eval p
    · have hex : ∃ j, f j ≠ 0 := by
        by_contra! h
        exact hz (funext h)
      obtain ⟨j, hj⟩ := hex
      let g : Fin 5 → ℕ := Function.update f j (f j - 1)
      have hsum : (∑ i, g i) < m := by
        rw [← hf]
        apply Finset.sum_lt_sum
        · intro i _
          by_cases hij : i = j
          · subst i
            simp only [g, Function.update_self]
            omega
          · simpa only [g, Function.update_of_ne hij] using Nat.le_refl (f i)
        · refine ⟨j, Finset.mem_univ j, ?_⟩
          simp only [g, Function.update_self]
          omega
      obtain ⟨q, hq, hqp⟩ := ih (∑ i, g i) hsum g rfl
      have hdecomp : f = Pi.single j 1 + g := by
        funext i
        by_cases hij : i = j
        · subst i
          simp only [Pi.add_apply, Pi.single_eq_same, g, Function.update_self]
          omega
        · simp only [Pi.add_apply, Pi.single_eq_of_ne hij, g, Function.update_of_ne hij,
            zero_add]
      have hd : degree f = degree g + if j.val < 2 then 1 else 2 := by
        rw [hdecomp, degree_add, degree_single, Nat.add_comm]
      refine ⟨wordOp j q, ?_, ?_⟩
      · simpa only [hd, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using wordOp_pure j hq
      · intro p
        rw [wordOp_eval j q (mon g) hqp p, hdecomp, mon_add, mon_single]
        simp only [Pi.mul_apply, pow_one]

private lemma delta_monomial_mem (e : Fin 5 → ℕ) :
    (fun p => delta p * mon e p) ∈ coordinates (degree e + 4) := by
  obtain ⟨q, hq, hep⟩ := invariant_multiple e
  have hm (l : List (Fin 2)) : (fun p => (word l p * commutator p).trace) =
      (fun p => (word (l ++ [0, 1]) p).trace) -
      (fun p => (word (l ++ [1, 0]) p).trace) := by
    funext p
    simp only [word_append, word_cons, word_nil, mul_one, Pi.sub_apply]
    change (word l p * (p 0 * p 1 - p 1 * p 0)).trace = _
    rw [mul_sub, Matrix.trace_sub]
  have hb (l : List (Fin 2)) (hl : l ∈ q.support) (b : List (Fin 2)) (hb : b.length = 2) :
      (fun p => (word (l ++ b) p).trace) ∈ coordinates (degree e + 4) := by
    have hd : (l ++ b).length = degree e + 4 := by
      rw [List.length_append, hq l hl, hb]
    simpa only [hd] using word_trace_mem (l ++ b)
  have htr : (fun p => (combinationEval q p * commutator p).trace) ∈
      coordinates (degree e + 4) := by
    have heq : (fun p => (combinationEval q p * commutator p).trace) =
        ∑ l ∈ q.support, q l • (fun p => (word l p * commutator p).trace) := by
      funext p
      change ((∑ l ∈ q.support, q l • word l p) * commutator p).trace = _
      simp only [Finset.sum_mul, smul_mul_assoc, Matrix.trace_sum, Matrix.trace_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [heq]
    apply (coordinates _).sum_mem
    intro l hl
    apply (coordinates _).smul_mem
    rw [hm]
    exact (coordinates _).sub_mem (hb l hl [0, 1] rfl) (hb l hl [1, 0] rfl)
  have heq : (fun p => (combinationEval q p * commutator p).trace) =
      (2 : ℂ) • (fun p => delta p * mon e p) := by
    funext p
    simp only [hep p, smul_mul_assoc, commutator_square, Matrix.trace_smul,
      Matrix.trace_one, Fintype.card_fin, smul_eq_mul, Pi.smul_apply]
    ring
  rw [heq] at htr
  exact ((coordinates _).smul_mem_iff (by norm_num : (2 : ℂ) ≠ 0)).mp htr

private lemma ordered_mem (n : ℕ) (a : Fin (n + 1)) : ordered n a ∈ coordinates n := by
  have hlen : (List.replicate a.val (0 : Fin 2) ++ List.replicate (n - a.val) 1).length =
      n := by
    simp only [List.length_append, List.length_replicate]
    omega
  have h := word_trace_mem (List.replicate a.val 0 ++ List.replicate (n - a.val) 1)
  rw [hlen] at h
  have heq : (fun p =>
      (word (List.replicate a.val 0 ++ List.replicate (n - a.val) 1) p).trace) =
      ordered n a := by
    funext p
    change _ = (p 0 ^ a.val * p 1 ^ (n - a.val)).trace
    rw [word_append, word_replicate, word_replicate]
  rw [heq] at h
  exact h

private lemma invariants_attained (z : Fin 5 → ℂ) (hz : z 0 ^ 2 ≠ 4 * z 2) :
    ∃ p : parameters, invariants p = z := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (z 0 ^ 2 - 4 * z 2) (n := 2) (by decide)
  have hr0 : r ≠ 0 := by
    intro h
    apply hz
    rw [h, zero_pow (by decide)] at hr
    linear_combination -hr
  let lam := (z 0 + r) / 2
  let mu := (z 0 - r) / 2
  have hsum : lam + mu = z 0 := by dsimp only [lam, mu]; ring
  have hprod : lam * mu = z 2 := by
    dsimp only [lam, mu]
    linear_combination -hr / 4
  have hd : lam - mu = r := by dsimp only [lam, mu]; ring
  have hne : lam - mu ≠ 0 := by rw [hd]; exact hr0
  clear_value lam mu
  let a := (z 4 - mu * z 1) / (lam - mu)
  let b := (lam * z 1 - z 4) / (lam - mu)
  have hab : a + b = z 1 := by
    dsimp only [a, b]
    field_simp [hne]
    ring
  have hw : lam * a + mu * b = z 4 := by
    dsimp only [a, b]
    field_simp [hne]
    ring
  clear_value a b
  refine ⟨![!![lam, 0; 0, mu], !![a, 1; a * b - z 3, b]], ?_⟩
  ext j
  fin_cases j <;>
    norm_num only [invariants, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.of_apply,
      Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one,
      mul_zero, zero_mul, one_mul, mul_one, add_zero, zero_add, sub_zero]
  · exact hsum
  · exact hab
  · exact hprod
  · ring <;> rfl
  · exact hw

private lemma invariant_polynomial_injective :
    Function.Injective (fun q : MvPolynomial (Fin 5) ℂ =>
      fun p : parameters => MvPolynomial.eval (invariants p) q) := by
  intro q r h
  let d : MvPolynomial (Fin 5) ℂ :=
    MvPolynomial.X 0 ^ 2 - MvPolynomial.C 4 * MvPolynomial.X 2
  have hd_eval (z : Fin 5 → ℂ) : MvPolynomial.eval z d = z 0 ^ 2 - 4 * z 2 := by
    simp only [d, map_sub, map_pow, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
  have hd : d ≠ 0 := by
    intro hd
    have he := congrArg (MvPolynomial.eval ![1, 0, 0, 0, 0]) hd
    rw [hd_eval, map_zero] at he
    norm_num at he
  have hmul : d * (q - r) = 0 := by
    apply MvPolynomial.funext
    intro z
    rw [map_mul, map_zero, hd_eval]
    by_cases hz : z 0 ^ 2 = 4 * z 2
    · rw [sub_eq_zero.mpr hz, zero_mul]
    · obtain ⟨p, hp⟩ := invariants_attained z hz
      have hh : MvPolynomial.eval z q = MvPolynomial.eval z r := by
        simpa only [hp] using congrFun h p
      rw [map_sub, hh, sub_self, mul_zero]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hd)

private lemma scalar_delta (x : ℂ) :
    delta (![x • 1, 1] : parameters) = 0 := by
  simp only [delta, invariants, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, mul_one, Matrix.trace_smul, Matrix.trace_one,
    Matrix.det_smul, Matrix.det_one, Fintype.card_fin, smul_eq_mul, mul_one]
  ring

private lemma scalar_ordered (n : ℕ) (a : Fin (n + 1)) (x : ℂ) :
    ordered n a (![x • 1, 1] : parameters) = 2 * x ^ a.val := by
  change ((x • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ^ a.val * 1 ^ (n - a.val)).trace = _
  simp only [smul_pow, one_pow, mul_one, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul]
  ring

private lemma normal_independent (n : ℕ) : LinearIndependent ℂ (normalFamily n) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hsplit (p : parameters) :
      (∑ a : Fin (n + 1), c (.inl a) * ordered n a p) +
      ∑ e : extraIndex n, c (.inr e) * (delta p * mon (fun j => (e.val j).val) p) = 0 := by
    have h := congrFun hc p
    rw [Fintype.sum_sum_type] at h
    simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, normalFamily, Sum.elim_inl, Sum.elim_inr] using h
  have hleft : ∀ a, c (.inl a) = 0 := by
    let q : Polynomial ℂ := ∑ a : Fin (n + 1), Polynomial.monomial a.val (c (.inl a))
    have hq : q = 0 := by
      apply Polynomial.funext
      intro x
      have h := hsplit (![x • 1, 1] : parameters)
      simp only [scalar_delta, scalar_ordered, zero_mul, mul_zero,
        Finset.sum_const_zero, add_zero] at h
      have he : q.eval x = ∑ a : Fin (n + 1), c (.inl a) * x ^ a.val := by
        simp only [q, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
      rw [Polynomial.eval_zero, he]
      have ht : (∑ a : Fin (n + 1), c (.inl a) * (2 * x ^ a.val)) =
          2 * ∑ a : Fin (n + 1), c (.inl a) * x ^ a.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      rw [ht] at h
      exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    intro a
    have h := congrArg (fun r : Polynomial ℂ => r.coeff a.val) hq
    simpa only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Fin.val_inj, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Polynomial.coeff_zero] using h
  let ex (e : extraIndex n) : Fin 5 →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun j => (e.val j).val)
  have hex : Function.Injective ex := by
    intro e f hef
    apply Subtype.ext
    funext j
    apply Fin.ext
    exact congrFun (congrArg (fun v : Fin 5 →₀ ℕ => (v : Fin 5 → ℕ)) hef) j
  let q : MvPolynomial (Fin 5) ℂ :=
    ∑ e : extraIndex n, MvPolynomial.monomial (ex e) (c (.inr e))
  let d : MvPolynomial (Fin 5) ℂ :=
    MvPolynomial.X 4 ^ 2 - MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 4 +
      MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 +
      MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 -
      MvPolynomial.C 4 * MvPolynomial.X 2 * MvPolynomial.X 3
  have hd (p : parameters) : MvPolynomial.eval (invariants p) d = delta p := by
    simp only [d, map_sub, map_add, map_pow, map_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    rfl
  have hq (p : parameters) : MvPolynomial.eval (invariants p) q =
      ∑ e : extraIndex n, c (.inr e) * mon (fun j => (e.val j).val) p := by
    simp only [q, map_sum, MvPolynomial.eval_monomial]
    apply Finset.sum_congr rfl
    intro e _
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  have hzero : d * q = 0 := by
    apply invariant_polynomial_injective
    funext p
    change MvPolynomial.eval (invariants p) (d * q) = MvPolynomial.eval (invariants p) 0
    rw [map_mul, hd, hq, map_zero, Finset.mul_sum]
    have h := hsplit p
    simp only [hleft, zero_mul, Finset.sum_const_zero, zero_add] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hd0 : d ≠ 0 := by
    intro h
    have hh := congrArg (MvPolynomial.eval ![0, 0, 0, 0, 1]) h
    norm_num [d] at hh
  have hq0 : q = 0 := (mul_eq_zero.mp hzero).resolve_left hd0
  intro i
  cases i with
  | inl a => exact hleft a
  | inr e =>
    have h := congrArg (fun r : MvPolynomial (Fin 5) ℂ => r.coeff (ex e)) hq0
    simpa only [q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
      hex.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      MvPolynomial.coeff_zero, Finsupp.zero_apply] using h

private lemma normal_span (n : ℕ) :
    Submodule.span ℂ (Set.range (normalFamily n)) = coordinates n := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    cases a with
    | inl a => exact ordered_mem n a
    | inr e =>
      have h := delta_monomial_mem (fun j => (e.val j).val)
      rw [e.property] at h
      exact h
  · apply (coordinates_upper n).trans
    apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · rintro f ⟨g, hg, rfl⟩
      change g ∈ Submodule.span ℂ _ at hg
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨e, he, rfl⟩ := hg
        have hdeg : degree e + 4 = n := by omega
        have hbound (j : Fin 5) : e j < n + 1 := by
          have h : e j ≤ degree e := by
            fin_cases j
            · change e 0 ≤ e 0 + e 1 + 2 * e 2 + 2 * e 3 + 2 * e 4
              omega
            · change e 1 ≤ e 0 + e 1 + 2 * e 2 + 2 * e 3 + 2 * e 4
              omega
            · change e 2 ≤ e 0 + e 1 + 2 * e 2 + 2 * e 3 + 2 * e 4
              omega
            · change e 3 ≤ e 0 + e 1 + 2 * e 2 + 2 * e 3 + 2 * e 4
              omega
            · change e 4 ≤ e 0 + e 1 + 2 * e 2 + 2 * e 3 + 2 * e 4
              omega
          omega
        let a : extraIndex n := ⟨(fun j => ⟨e j, hbound j⟩), hdeg⟩
        exact Submodule.subset_span ⟨Sum.inr a, rfl⟩
      | zero => simpa only [map_zero] using
          (Submodule.span ℂ (Set.range (normalFamily n))).zero_mem
      | add f g _ _ hf hg =>
        rw [map_add]
        exact (Submodule.span ℂ (Set.range (normalFamily n))).add_mem hf hg
      | smul c f _ hf =>
        rw [map_smul]
        exact (Submodule.span ℂ (Set.range (normalFamily n))).smul_mem c hf

/-- The dimension of the span of trace coordinates in the source parametrization. -/
theorem coordinate_dimension (n : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range fun i : Fin n → Fin 2 =>
      fun p : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ => traceWord 2 2 n p i)) =
      (n + 1) + Fintype.card {e : Fin 5 → Fin (n + 1) //
        (e 0).val + (e 1).val + 2 * (e 2).val + 2 * (e 3).val + 2 * (e 4).val + 4 = n} := by
  change Module.finrank ℂ (coordinates n) = (n + 1) + Fintype.card (extraIndex n)
  rw [← normal_span, finrank_span_eq_card (normal_independent n)]
  change Fintype.card (Fin (n + 1) ⊕ extraIndex n) = _
  rw [Fintype.card_sum, Fintype.card_fin]

end

end D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords
