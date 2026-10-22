/- GID: D5/S3/Quantum/Codes/QuditStabilizerProductVector
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Uniform qudit Pauli words, their commutation form, and the product-vector obstruction. -/

module

public import D5.S3.Observer.WindowRegister
public import D5.S3.Quantum.Algebra.WeylDisplacementTrace
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open D5.S3.Observer.WindowRegister

namespace D5.S3.Quantum.Codes.QuditStabilizerProductVector

noncomputable section

structure PauliWord (N p : ℕ) where
  phase : ZMod p
  x : Fin N → ZMod p
  z : Fin N → ZMod p

def localSymplectic {p : ℕ} (x z x' z' : ZMod p) : ZMod p :=
  z * x' - x * z'

def localPauli (p : ℕ) [NeZero p] (x z : ZMod p) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  shiftMatrix p ^ x.val * clockMatrix p ^ z.val

def pauliWordOperator {N p : ℕ} [NeZero p] (w : PauliWord N p) :
    Matrix (Fin N → ZMod p) (Fin N → ZMod p) ℂ :=
  (windowRoot p ^ w.phase.val) • Matrix.of (fun u v =>
    ∏ n, localPauli p (w.x n) (w.z n) (u n) (v n))

def wordMul {N p : ℕ} (a b : PauliWord N p) : PauliWord N p :=
  { phase := a.phase + b.phase
    x := a.x + b.x
    z := a.z + b.z }

def commutationVector {N p : ℕ} (a b : PauliWord N p) : Fin N → ZMod p :=
  fun n => localSymplectic (a.x n) (a.z n) (b.x n) (b.z n)

theorem local_pauli_commutation {p : ℕ} [NeZero p]
    (x z x' z' : ZMod p) :
    localPauli p x z * localPauli p x' z' =
      windowRoot p ^ (localSymplectic x z x' z').val •
        (localPauli p x' z' * localPauli p x z) := by
  sorry

theorem pauli_word_mul {N p : ℕ} [NeZero p]
    (a b : PauliWord N p) :
    pauliWordOperator a * pauliWordOperator b =
      windowRoot p ^ (∑ n, commutationVector a b n).val •
        pauliWordOperator (wordMul a b) := by
  sorry

theorem pauli_word_commutation {N p : ℕ} [NeZero p]
    (a b : PauliWord N p) :
    pauliWordOperator a * pauliWordOperator b =
      windowRoot p ^ (∑ n, commutationVector a b n).val •
        (pauliWordOperator b * pauliWordOperator a) := by
  sorry

theorem pauli_word_trace_zero {N p : ℕ} [NeZero p]
    (w : PauliWord N p) (h : ∃ n, w.x n ≠ 0 ∨ w.z n ≠ 0) :
    Matrix.trace (pauliWordOperator w) = 0 := by
  sorry

theorem common_fixed_subspace_nontrivial {N p : ℕ} [NeZero p]
    (S : Finset (PauliWord N p))
    (hcomm : ∀ a ∈ S, ∀ b ∈ S,
      Commute (pauliWordOperator a) (pauliWordOperator b))
    (hscalar : ∀ a ∈ S, pauliWordOperator a = 1 → a.phase = 0 ∧ a.x = 0 ∧ a.z = 0) :
    ∃ ψ : (Fin N → ZMod p) → ℂ, ψ ≠ 0 ∧
      ∀ a ∈ S, (pauliWordOperator a).mulVec ψ = ψ := by
  sorry

theorem product_vector_of_restricted_commuting {N p : ℕ} [NeZero p]
    (S : Finset (PauliWord N p)) (Q : Set (Fin N))
    (hQ : Q.Nonempty) (hQc : Qᶜ.Nonempty)
    (hcommQ : ∀ a ∈ S, ∀ b ∈ S,
      ∑ n : Q, commutationVector a b n.1 = 0)
    (hV : ∃ ψ : (Fin N → ZMod p) → ℂ, ψ ≠ 0 ∧
      ∀ a ∈ S, (pauliWordOperator a).mulVec ψ = ψ) :
    ∃ ψ : (Fin N → ZMod p) → ℂ, ψ ≠ 0 ∧
      (∃ u : (Q → ZMod p) → ℂ, ∃ v : (Qᶜ → ZMod p) → ℂ,
        ∀ x, ψ x = u (fun q => x q.1) * v (fun q => x q.1)) := by
  sorry

end

end D5.S3.Quantum.Codes.QuditStabilizerProductVector

end
