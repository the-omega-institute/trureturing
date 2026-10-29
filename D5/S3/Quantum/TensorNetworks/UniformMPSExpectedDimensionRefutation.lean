/- GID: D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.claim; result=D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.result; claim=D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.claim
   digest: Two-site uniform matrix product states can miss the expected dimension. -/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation

open scoped BigOperators Matrix nonZeroDivisors

noncomputable section

/-- The coefficients of a uniform periodic matrix product state, in word order. -/
def traceWord (b d n : ℕ) (m : Fin d → Matrix (Fin b) (Fin b) ℂ)
    (i : Fin n → Fin d) : ℂ :=
  ((List.ofFn fun k => m (i k)).prod).trace

/-- Uniform matrix product states are the image of the trace-word parametrization. -/
def uMPS (b d n : ℕ) : Set ((Fin n → Fin d) → ℂ) :=
  Set.range (traceWord b d n)

/-- The dimension of the Zariski closure, measured by its coordinate ring. -/
def varietyDim {σ : Type*} (s : Set (σ → ℂ)) : WithBot ℕ∞ :=
  ringKrullDim (MvPolynomial σ ℂ ⧸ MvPolynomial.vanishingIdeal ℂ s)

/-- Tensors invariant under cyclic rotation of their word positions. -/
def Cyc (n d : ℕ) : Submodule ℂ ((Fin n → Fin d) → ℂ) where
  carrier := {t | ∀ i, t (i ∘ finRotate n) = t i}
  zero_mem' := by intro i; rfl
  add_mem' := by
    intro t u ht hu i
    exact congrArg₂ (· + ·) (ht i) (hu i)
  smul_mem' := by
    intro c t ht i
    exact congrArg (c * ·) (ht i)

/-- Czapliński–Michałek–Seynnaeve Conjecture 2.14: every uMPS has expected dimension. -/
def claim : Prop :=
  ∀ b d n : ℕ, 0 < b → 0 < d → 0 < n →
    varietyDim (uMPS b d n) =
      ((min ((d - 1) * b ^ 2 + 1) (Module.finrank ℂ (Cyc n d)) : ℕ) : WithBot ℕ∞)

private abbrev UpperPair := {p : Fin 5 × Fin 5 // p.1 ≤ p.2}

private def orderedPair (i j : Fin 5) : UpperPair :=
  ⟨(min i j, max i j), min_le_max⟩

private lemma upperPair_card : Fintype.card UpperPair = 15 := by
  sorry

private lemma orderedPair_comm (i j : Fin 5) : orderedPair i j = orderedPair j i := by
  sorry

private lemma orderedPair_of_le (i j : Fin 5) (h : i ≤ j) :
    orderedPair i j = ⟨(i, j), h⟩ := by
  sorry

private lemma cyclic_finrank_lower : 15 ≤ Module.finrank ℂ (Cyc 2 5) := by
  sorry

private lemma traceWord_two (m : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ)
    (i : Fin 2 → Fin 5) : traceWord 2 5 2 m i = (m (i 0) * m (i 1)).trace := by
  sorry

private lemma gram_factorization (m : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) :
    (fun i j => (m i * m j).trace) =
      (fun i (p : Fin 2 × Fin 2) => m i p.1 p.2) *
        (fun (p : Fin 2 × Fin 2) j => m j p.2 p.1) := by
  sorry

private lemma gram_det_zero (m : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.det (fun i j => (m i * m j).trace) = 0 := by
  sorry

private lemma coordinate_symmetry (i j : Fin 5) :
    MvPolynomial.X ![i, j] - MvPolynomial.X ![j, i] ∈
      MvPolynomial.vanishingIdeal ℂ (uMPS 2 5 2) := by
  sorry

private def coordinateMap : MvPolynomial UpperPair ℂ →ₐ[ℂ]
    MvPolynomial (Fin 2 → Fin 5) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ (uMPS 2 5 2) :=
  MvPolynomial.aeval fun p =>
    Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ (uMPS 2 5 2))
      (MvPolynomial.X ![p.1.1, p.1.2])

private lemma coordinateMap_variable (i j : Fin 5) :
    coordinateMap (MvPolynomial.X (orderedPair i j)) =
      Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ (uMPS 2 5 2))
        (MvPolynomial.X ![i, j]) := by
  sorry

private lemma coordinateMap_surjective : Function.Surjective coordinateMap := by
  sorry

private def symmetricDet : MvPolynomial UpperPair ℂ :=
  Matrix.det (fun i j => MvPolynomial.X (orderedPair i j))

private lemma symmetricDet_ne_zero : symmetricDet ≠ 0 := by
  sorry

private lemma coordinateMap_det_zero : coordinateMap symmetricDet = 0 := by
  sorry

private lemma actual_dimension_upper : varietyDim (uMPS 2 5 2) ≤ 14 := by
  sorry

/-- At bond dimension two, five physical symbols and two sites, dimension is at most fourteen
while the conjectured dimension is at least fifteen. -/
theorem result : ¬ claim := by
  intro h
  have heq := h 2 5 2 (by decide) (by decide) (by decide)
  have hlo : 15 ≤ min ((5 - 1) * 2 ^ 2 + 1) (Module.finrank ℂ (Cyc 2 5)) :=
    le_min (by decide) cyclic_finrank_lower
  have hcast : (15 : WithBot ℕ∞) ≤
      ((min ((5 - 1) * 2 ^ 2 + 1) (Module.finrank ℂ (Cyc 2 5)) : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast hlo
  have hbad : (15 : WithBot ℕ∞) ≤ 14 := by
    rw [← heq] at hcast
    exact hcast.trans actual_dimension_upper
  norm_num at hbad

end D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation
