/- GID: D5/S1/Recurrence/CostaCatarinoBidimensionalFibonacci
   generality: I
   mirror-B: D5/B/S1/Recurrence/CostaCatarinoBidimensionalFibonacci
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every bidimensional Fibonacci matrix has nonzero determinant. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#22448; Proved).
Direct frozen dependencies: D5/S1/Recurrence/FibVajda.fib_vajda
  declaration statement_id: sha256:68cf09f524d730d13c876dd486737247ac0bf595476fa92c2f5a9e5b5b080e65.
The following declarations have proof_shape: bind-only; escape_witness: none.
IsSourceSequence: frozen dependencies: none; consumers: claim, closed_form_is_source, source_unique.
sourceClosedForm: frozen dependencies: none; consumers: closed_form_is_source, determinant_im, result.
sourceMatrix: frozen dependencies: none; consumers: claim, determinant_im, determinant_im_ne_zero, result.
claim: frozen dependencies: none; consumer: result.
P: frozen dependencies: none; consumers: signed_identity, determinant_im.
closed_form_is_source: frozen dependencies: none; consumer: result.
source_unique: frozen dependencies: none; consumer: result.
signed_identity: frozen dependencies: Vajda above; consumer: determinant_im.
t_pos: frozen dependencies: none; consumer: determinant_im_ne_zero.
t_strictMono: frozen dependencies: none; consumer: determinant_im_ne_zero.
determinant_im: frozen dependencies: Vajda above; consumer: determinant_im_ne_zero.
determinant_im_ne_zero: frozen dependencies: Vajda above; consumer: result.
The public definitions reproduce Definition 2.1, Lemma 2.5 and Definition 3.1;
claim includes existence and both natural-index axes. Vajda is specialized to shifts one and two.
Consecutive Fibonacci products are written directly; no duplicate scalar definition is introduced.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22505.
-/

import D5.S1.Recurrence.FibVajda
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Nat.Fib.Basic

namespace D5.S1.Recurrence.CostaCatarinoBidimensionalFibonacci

/-- Definition 2.1, including both recurrences and all four initial terms.
The guarded subtractions reproduce (2.1) and (2.2) at their stated indices. -/
def IsSourceSequence (f : ℕ → ℕ → ℂ) : Prop :=
  (∀ (m n : ℕ), 2 ≤ m → f m n = f (m - 1) n + f (m - 2) n) ∧
  (∀ (m n : ℕ), 2 ≤ n → f m n = f m (n - 1) + f m (n - 2)) ∧
  f 0 0 = 0 ∧ f 1 0 = 1 ∧ f 0 1 = Complex.I ∧ f 1 1 = 1 + Complex.I

/-- Lemma 2.5, equation (2.6), with Mathlib's ordinary Fibonacci sequence. -/
def sourceClosedForm (m n : ℕ) : ℂ :=
  (Nat.fib m : ℂ) * (Nat.fib (n + 1) : ℂ) +
    Complex.I * (Nat.fib (m + 1) : ℂ) * (Nat.fib n : ℂ)

/-- Definition 3.1, equation (3.1), retaining both minus signs. -/
def sourceMatrix (f : ℕ → ℕ → ℂ) (m n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![f (m + 2) (n + 2), -f (m + 1) (n + 1);
     f (m + 1) (n + 1), -f m n]

/-- The unnumbered Conjecture at the end of section 4, p. 73.
Existence prevents a vacuous universal assertion about the recursively specified sequence. -/
def claim : Prop :=
  (∃ f : ℕ → ℕ → ℂ, IsSourceSequence f) ∧
    ∀ f : ℕ → ℕ → ℂ, IsSourceSequence f →
      ∀ m : ℕ, ∀ n : ℕ, (sourceMatrix f m n).det ≠ 0

end D5.S1.Recurrence.CostaCatarinoBidimensionalFibonacci

namespace D5.S1.Recurrence.CostaCatarinoBidimensionalFibonacci

private theorem closed_form_is_source : IsSourceSequence sourceClosedForm := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m n hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    simp only [sourceClosedForm, Nat.add_sub_cancel,
      Nat.reduceSubDiff, Nat.fib_add_two, Nat.cast_add]
    ring
  · intro m n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    simp only [sourceClosedForm, Nat.add_sub_cancel,
      Nat.reduceSubDiff, Nat.fib_add_two, Nat.cast_add]
    ring
  all_goals norm_num [sourceClosedForm]

private theorem source_unique (f g : ℕ → ℕ → ℂ)
    (hf : IsSourceSequence f) (hg : IsSourceSequence g) : f = g := by
  let E : LinearRecurrence ℂ := ⟨2, fun _ => 1⟩
  have unique1 (u v : ℕ → ℂ)
      (hu : ∀ n, u (n + 2) = u (n + 1) + u n)
      (hv : ∀ n, v (n + 2) = v (n + 1) + v n)
      (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
    have hu' : E.IsSolution u := by
      intro n
      simpa [E, Fin.sum_univ_two, add_comm] using hu n
    have hv' : E.IsSolution v := by
      intro n
      simpa [E, Fin.sum_univ_two, add_comm] using hv n
    apply (E.eq_iff_eqOn_range_order u v hu' hv').2
    intro k hk
    have hk' : k < 2 := Finset.mem_range.mp hk
    interval_cases k <;> assumption
  have rm (u : ℕ → ℕ → ℂ) (hu : IsSourceSequence u) (m n : ℕ) :
      u (m + 2) n = u (m + 1) n + u m n := by
    simpa only [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega]
      using hu.1 (m + 2) n (by omega)
  have rn (u : ℕ → ℕ → ℂ) (hu : IsSourceSequence u) (m n : ℕ) :
      u m (n + 2) = u m (n + 1) + u m n := by
    simpa only [Nat.add_sub_cancel, show n + 2 - 1 = n + 1 by omega]
      using hu.2.1 m (n + 2) (by omega)
  have row0 : f 0 = g 0 := unique1 (f 0) (g 0) (rn f hf 0) (rn g hg 0)
    (hf.2.2.1.trans hg.2.2.1.symm) (hf.2.2.2.2.1.trans hg.2.2.2.2.1.symm)
  have row1 : f 1 = g 1 := unique1 (f 1) (g 1) (rn f hf 1) (rn g hg 1)
    (hf.2.2.2.1.trans hg.2.2.2.1.symm) (hf.2.2.2.2.2.trans hg.2.2.2.2.2.symm)
  funext m n
  exact congrFun (unique1 (fun i => f i n) (fun i => g i n)
    (fun i => rm f hf i n) (fun i => rm g hg i n)
    (congrFun row0 n) (congrFun row1 n)) m

private def P (r : ℕ) : ℝ := (Nat.fib r : ℝ) * Nat.fib (r + 3)

private theorem signed_identity (r : ℕ) : ((Nat.fib (r + 1) : ℝ) * Nat.fib (r + 2)) - P r = (-1 : ℝ) ^ r := by
  have h := D5.S1.Recurrence.FibVajda.fib_vajda r 1 2
  norm_num [Nat.add_assoc] at h
  dsimp only [P]
  exact_mod_cast h

private theorem t_pos (r : ℕ) : 0 < ((Nat.fib (r + 1) : ℝ) * Nat.fib (r + 2)) := by
  exact mul_pos (by exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < r + 1)))
    (by exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < r + 2)))

private theorem t_strictMono : StrictMono (fun r : ℕ => (Nat.fib (r + 1) : ℝ) * Nat.fib (r + 2)) := by
  have hm : Monotone (fun r : ℕ => (Nat.fib (r + 1) : ℝ)) := by
    intro a b hab
    change (Nat.fib (a + 1) : ℝ) ≤ (Nat.fib (b + 1) : ℝ)
    exact_mod_cast (Nat.fib_mono (Nat.add_le_add_right hab 1))
  have hs : StrictMono (fun r : ℕ => (Nat.fib (r + 2) : ℝ)) := by
    intro a b hab
    change (Nat.fib (a + 2) : ℝ) < (Nat.fib (b + 2) : ℝ)
    exact_mod_cast (Nat.fib_add_two_strictMono hab)
  have hp : ∀ r : ℕ, 0 < (Nat.fib (r + 1) : ℝ) := by
    intro r
    exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < r + 1))
  exact hm.mul_strictMono hs hp (fun r => by positivity)

private theorem determinant_im (m n : ℕ) :
    (sourceMatrix sourceClosedForm m n).det.im =
      (-1 : ℝ) ^ m * ((Nat.fib (n + 1) : ℝ) * Nat.fib (n + 2)) + (-1 : ℝ) ^ n * ((Nat.fib (m + 1) : ℝ) * Nat.fib (m + 2)) := by
  rw [← signed_identity m, ← signed_identity n]
  simp only [sourceMatrix, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    sourceClosedForm, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.sub_im,
    Complex.natCast_re, Complex.natCast_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, one_mul, add_zero, zero_add, sub_zero,
    P, Nat.add_assoc, Nat.reduceAdd]
  ring

private theorem determinant_im_ne_zero (m n : ℕ) :
    (sourceMatrix sourceClosedForm m n).det.im ≠ 0 := by
  rw [determinant_im]
  intro hz
  have hm := t_pos m
  have hn := t_pos n
  rcases neg_one_pow_eq_or ℝ m with hms | hms <;>
    rcases neg_one_pow_eq_or ℝ n with hns | hns
  · rw [hms, hns] at hz
    linarith
  · have heq : ((Nat.fib (m + 1) : ℝ) * Nat.fib (m + 2)) = ((Nat.fib (n + 1) : ℝ) * Nat.fib (n + 2)) := by rw [hms, hns] at hz; linarith
    have hmn := t_strictMono.injective heq
    subst n
    linarith
  · have heq : ((Nat.fib (m + 1) : ℝ) * Nat.fib (m + 2)) = ((Nat.fib (n + 1) : ℝ) * Nat.fib (n + 2)) := by rw [hms, hns] at hz; linarith
    have hmn := t_strictMono.injective heq
    subst n
    linarith
  · rw [hms, hns] at hz
    linarith

theorem result : D5.S1.Recurrence.CostaCatarinoBidimensionalFibonacci.claim := by
  refine ⟨⟨sourceClosedForm, closed_form_is_source⟩, ?_⟩
  intro f hf m n
  have heq := source_unique f sourceClosedForm hf closed_form_is_source
  subst f
  intro hzero
  exact determinant_im_ne_zero m n (by rw [hzero]; rfl)

end D5.S1.Recurrence.CostaCatarinoBidimensionalFibonacci
