/- GID: D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.claim; result=D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.result; claim=D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.claim
   digest: Order nine obstructs the conjectured odd-order minimum of Hadamardness. -/

import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! The sign-matrix Hadamardness conjecture of Singh and Nechita,
arXiv:2112.11123v1, equation `eq:Hada_measure` and the conjecture following its table.
The integer trace equals the source's real trace for real sign matrices.
admission_basis: open-problem-resolution
-/

open Matrix
open scoped BigOperators

namespace D5.S3.Quantum.Matrix.SinghNechitaOddHadamardnessRefutation

/-- Every entry is one of the two real signs, represented exactly as integers. -/
def IsSignMatrix {d : ℕ} (c : Matrix (Fin d) (Fin d) ℤ) : Prop :=
  ∀ i j, c i j = 1 ∨ c i j = -1

/-- The trace of the square of the row Gram matrix. -/
def hadamardness {d : ℕ} (c : Matrix (Fin d) (Fin d) ℤ) : ℤ :=
  Matrix.trace ((c * cᵀ) * (c * cᵀ))

/-- In every odd order the stated value is attained and is a lower bound. -/
def claim : Prop :=
  ∀ d : ℕ, Odd d →
    ∃ c : Matrix (Fin d) (Fin d) ℤ,
      IsSignMatrix c ∧ hadamardness c = ((d ^ 3 + d * (d - 1) : ℕ) : ℤ) ∧
      ∀ b : Matrix (Fin d) (Fin d) ℤ, IsSignMatrix b →
        ((d ^ 3 + d * (d - 1) : ℕ) : ℤ) ≤ hadamardness b

private lemma equality_forces_unit (c : Matrix (Fin 9) (Fin 9) ℤ)
    (hc : IsSignMatrix c) (he : hadamardness c = 801) :
    ∀ i j, i ≠ j → (c * cᵀ) i j = 1 ∨ (c * cᵀ) i j = -1 := by
  sorry

private lemma normalize_gram (c : Matrix (Fin 9) (Fin 9) ℤ)
    (hc : IsSignMatrix c)
    (hu : ∀ i j, i ≠ j → (c * cᵀ) i j = 1 ∨ (c * cᵀ) i j = -1) :
    ∃ b : Matrix (Fin 9) (Fin 9) ℤ,
      b * bᵀ = (8 : ℤ) • 1 + Matrix.of (fun _ _ => 1) := by
  sorry

private lemma gram_impossible (b : Matrix (Fin 9) (Fin 9) ℤ)
    (hb : b * bᵀ = (8 : ℤ) • 1 + Matrix.of (fun _ _ => 1)) : False := by
  sorry

theorem result : ¬ claim := by
  intro h
  obtain ⟨c, hc, he, _⟩ := h 9 (by decide)
  norm_num at he
  obtain ⟨b, hb⟩ := normalize_gram c hc (equality_forces_unit c hc he)
  exact gram_impossible b hb

end D5.S3.Quantum.Matrix.SinghNechitaOddHadamardnessRefutation
