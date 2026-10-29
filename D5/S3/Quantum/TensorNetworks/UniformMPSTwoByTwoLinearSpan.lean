/- GID: D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The linear span of binary bond-two uniform matrix product states. -/

import D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan

open scoped BigOperators Matrix
open UniformMPSExpectedDimensionRefutation (traceWord uMPS)

noncomputable section

/-- De Lazzari–Motwani–Seynnaeve Conjecture 3.8, for positive word lengths. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (Module.finrank ℂ (Submodule.span ℂ (uMPS 2 2 n)) : ℚ) =
      if Even n then ((n : ℚ) ^ 4 - 4 * n ^ 2 + 192 * n + 192) / 192
      else ((n : ℚ) ^ 4 - 10 * n ^ 2 + 192 * n + 201) / 192

private def parameters := Fin 2 → Matrix (Fin 2) (Fin 2) ℂ

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

private def extraIndex (n : ℕ) :=
  {e : Fin 5 → Fin (n + 1) // degree (fun j => (e j).val) + 4 = n}

private def normalIndex (n : ℕ) := Fin (n + 1) ⊕ extraIndex n

private def normalFamily (n : ℕ) : normalIndex n → parameters → ℂ :=
  Sum.elim (ordered n) (fun e p => delta p * mon (fun j => (e.val j).val) p)

private lemma mon_add (e f : Fin 5 → ℕ) : mon (e + f) = mon e * mon f := by
  sorry

private lemma graded_mul {i j : ℤ} {f g : parameters → ℂ}
    (hf : f ∈ graded i) (hg : g ∈ graded j) : f * g ∈ graded (i + j) := by
  sorry

private lemma cayley_hamilton (x : Matrix (Fin 2) (Fin 2) ℂ) :
    x * x = x.trace • x - x.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  sorry

private lemma polarized_cayley_hamilton (x y : Matrix (Fin 2) (Fin 2) ℂ) :
    y * x = x.trace • y + y.trace • x +
      ((x * y).trace - x.trace * y.trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - x * y := by
  sorry

private lemma sandwich (x y : Matrix (Fin 2) (Fin 2) ℂ) :
    y * x * y = (x * y).trace • y + y.det • x -
      (x.trace * y.det) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  sorry

private lemma word_reduction (l : List (Fin 2)) :
    ∃ r : Fin 4 → parameters → ℂ,
      r 0 ∈ graded l.length ∧ r 1 ∈ graded ((l.length : ℤ) - 1) ∧
      r 2 ∈ graded ((l.length : ℤ) - 1) ∧ r 3 ∈ graded ((l.length : ℤ) - 2) ∧
      ∀ p, word l p = r 0 p • 1 + r 1 p • p 0 + r 2 p • p 1 +
        r 3 p • (p 0 * p 1) := by
  sorry

private lemma commutator_traces (p : parameters) :
    (commutator p).trace = 0 ∧ (p 0 * commutator p).trace = 0 ∧
      (p 1 * commutator p).trace = 0 ∧ (p 0 * p 1 * commutator p).trace = delta p := by
  sorry

private lemma trace_word_commutator (l : List (Fin 2)) :
    (fun p => (word l p * commutator p).trace) ∈
      (graded ((l.length : ℤ) - 2)).map deltaMap := by
  sorry

private lemma coordinates_upper (n : ℕ) :
    coordinates n ≤ Submodule.span ℂ (Set.range (ordered n)) ⊔
      (graded ((n : ℤ) - 4)).map deltaMap := by
  sorry

private def combinationEval (q : List (Fin 2) →₀ ℂ) (p : parameters) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  q.sum fun l c => c • word l p

private lemma commutator_operations (p : parameters) :
    p 0 * commutator p + commutator p * p 0 = invariants p 0 • commutator p ∧
    p 1 * commutator p + commutator p * p 1 = invariants p 1 • commutator p ∧
    p 0 * commutator p * p 0 = invariants p 2 • commutator p ∧
    p 1 * commutator p * p 1 = invariants p 3 • commutator p ∧
    p 0 * p 1 * commutator p + commutator p * p 1 * p 0 =
      invariants p 4 • commutator p := by
  sorry

private lemma commutator_square (p : parameters) :
    commutator p * commutator p = delta p • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  sorry

private lemma invariant_multiple (e : Fin 5 → ℕ) :
    ∃ q : List (Fin 2) →₀ ℂ,
      (∀ l ∈ q.support, l.length = degree e + 2) ∧
      ∀ p, combinationEval q p = mon e p • commutator p := by
  sorry

private lemma delta_monomial_mem (e : Fin 5 → ℕ) :
    (fun p => delta p * mon e p) ∈ coordinates (degree e + 4) := by
  sorry

private lemma ordered_mem (n : ℕ) (a : Fin (n + 1)) : ordered n a ∈ coordinates n := by
  sorry

private lemma invariants_attained (z : Fin 5 → ℂ) (hz : z 0 ^ 2 ≠ 4 * z 2) :
    ∃ p : parameters, invariants p = z := by
  sorry

private lemma invariant_polynomial_injective :
    Function.Injective (fun q : MvPolynomial (Fin 5) ℂ =>
      fun p : parameters => MvPolynomial.eval (invariants p) q) := by
  sorry

private lemma normal_independent (n : ℕ) : LinearIndependent ℂ (normalFamily n) := by
  sorry

private lemma normal_span (n : ℕ) :
    Submodule.span ℂ (Set.range (normalFamily n)) = coordinates n := by
  sorry

private lemma evaluation_bridge (n : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ (uMPS 2 2 n)) =
      Module.finrank ℂ (coordinates n) := by
  sorry

private lemma coordinate_dimension (n : ℕ) :
    Module.finrank ℂ (coordinates n) = Fintype.card (normalIndex n) := by
  sorry

private lemma monomial_count_even (k : ℕ) :
    (Fintype.card (extraIndex (2 * k)) : ℚ) =
      ((2 * k : ℚ) ^ 4 - 4 * (2 * k) ^ 2) / 192 := by
  sorry

private lemma monomial_count_odd (k : ℕ) :
    (Fintype.card (extraIndex (2 * k + 1)) : ℚ) =
      ((2 * k + 1 : ℚ) ^ 4 - 10 * (2 * k + 1) ^ 2 + 9) / 192 := by
  sorry

private lemma normal_count (n : ℕ) (hn : 1 ≤ n) :
    (Fintype.card (normalIndex n) : ℚ) =
      if Even n then ((n : ℚ) ^ 4 - 4 * n ^ 2 + 192 * n + 192) / 192
      else ((n : ℚ) ^ 4 - 10 * n ^ 2 + 192 * n + 201) / 192 := by
  sorry

/-- The exact complex dimension of the span of binary bond-two uniform MPS. -/
theorem result : claim := by
  intro n hn
  rw [evaluation_bridge, coordinate_dimension]
  exact normal_count n hn

end

end D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan
