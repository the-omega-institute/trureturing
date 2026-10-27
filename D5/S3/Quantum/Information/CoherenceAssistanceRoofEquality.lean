/- GID: D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/CoherenceAssistanceRoofEquality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.claim; result=D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.result; claim=D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.claim
   digest: A rank-two state in four dimensions has equal coherence roofs. -/

module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Trace
public import D5.S3.Quantum.Measurement.AntidistinguishabilityGram
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option linter.style.longLine false
open scoped BigOperators ComplexOrder
open Matrix

@[expose] public section
noncomputable section
namespace D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality

/-- The source class of symmetric concave functions on the probability simplex.
Vanishing at every vertex is equivalent, by symmetry, to vanishing at the first vertex. -/
def IsCoherenceFunction {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ConcaveOn ℝ (stdSimplex ℝ (Fin n)) f ∧
    (∀ σ : Equiv.Perm (Fin n), ∀ p ∈ stdSimplex ℝ (Fin n), f (p ∘ σ) = f p) ∧
    ∀ i : Fin n, f (Pi.single i 1) = 0

/-- Squared absolute values of the amplitudes in the fixed reference basis. -/
def coherenceVector {n : ℕ} (ψ : Fin n → ℂ) : Fin n → ℝ :=
  fun i => Complex.normSq (ψ i)

/-- All finite pure-state decompositions, with Hilbert norm one for every vector. -/
def IsDecomposition {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (p : Fin k → ℝ) (ψ : Fin k → Fin n → ℂ) : Prop :=
  (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
    (∀ j, ∑ i, Complex.normSq (ψ j i) = 1) ∧
    ρ = ∑ j, (p j : ℂ) • vecMulVec (ψ j) (star (ψ j))

/-- The source averages over all finite pure-state decompositions. -/
def decompositionValues {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : Set ℝ :=
  {x | ∃ k p ψ, IsDecomposition ρ k p ψ ∧ x = ∑ j, p j * f (coherenceVector (ψ j))}

noncomputable def convexRoof {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ := sInf (decompositionValues f ρ)

noncomputable def assistance {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ := sSup (decompositionValues f ρ)

/-- A density matrix with purity different from one; for density matrices this
is equivalent to not being a unit rank-one projector. -/
def IsMixed {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1 ∧ (ρ * ρ).trace ≠ 1

/-- The universal strict gap asked for in arXiv:2103.08818v1. -/
def claim : Prop :=
  ∀ n : ℕ, ∀ f : (Fin n → ℝ) → ℝ, IsCoherenceFunction f →
    (∃ p ∈ stdSimplex ℝ (Fin n), f p ≠ 0) →
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, IsMixed ρ → convexRoof f ρ < assistance f ρ

private def quadratic (p : Fin 4 → ℝ) : ℝ := 1 - ∑ i, p i ^ 2

private def omega : ℂ := (-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2

private def v : Fin 4 → ℂ :=
  ![(Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 6 : ℂ)⁻¹,
    (Real.sqrt 6 : ℂ)⁻¹, (Real.sqrt 6 : ℂ)⁻¹]

private def w : Fin 4 → ℂ :=
  ![0, (Real.sqrt 3 : ℂ)⁻¹, omega / (Real.sqrt 3 : ℂ),
    omega ^ 2 / (Real.sqrt 3 : ℂ)]

private def projection : Matrix (Fin 4) (Fin 4) ℂ :=
  vecMulVec v (star v) + vecMulVec w (star w)

private def rho : Matrix (Fin 4) (Fin 4) ℂ := (1 / 2 : ℂ) • projection

private lemma frame :
    star v ⬝ᵥ v = 1 ∧ star w ⬝ᵥ w = 1 ∧ star v ⬝ᵥ w = 0 ∧ star w ⬝ᵥ v = 0 ∧
      (∑ i, Complex.normSq (v i)) = 1 ∧ (∑ i, Complex.normSq (w i)) = 1 := by
  sorry

private lemma projection_properties :
    projection.IsHermitian ∧ projection * projection = projection ∧
      ((1 - projection) * rho).trace = 0 := by
  sorry

private lemma decomposition_support {n k : ℕ}
    (ρ q : Matrix (Fin n) (Fin n) ℂ) (p : Fin k → ℝ) (ψ : Fin k → Fin n → ℂ)
    (hd : IsDecomposition ρ k p ψ) (hq : q.PosSemidef) (hzero : (q * ρ).trace = 0)
    (j : Fin k) (hp : 0 < p j) : q *ᵥ ψ j = 0 := by
  sorry

private lemma fourth_moment (a b : ℂ) :
    (∑ i, Complex.normSq (a * v i + b * w i) ^ 2) =
      (Complex.normSq a + Complex.normSq b) ^ 2 / 3 := by
  sorry

private lemma unit_span_value (ψ : Fin 4 → ℂ)
    (hunit : ∑ i, Complex.normSq (ψ i) = 1)
    (hspan : (1 - projection) *ᵥ ψ = 0) : quadratic (coherenceVector ψ) = 2 / 3 := by
  sorry

private lemma quadratic_coherence : IsCoherenceFunction quadratic := by
  sorry

private lemma quadratic_nonzero :
    ∃ p ∈ stdSimplex ℝ (Fin 4), quadratic p ≠ 0 := by
  sorry

private lemma witness_decomposition :
    IsDecomposition rho 2 (fun _ => 1 / 2) ![v, w] := by
  sorry

private lemma values_singleton : decompositionValues quadratic rho = {2 / 3} := by
  have hproj := projection_properties
  have hq := D5.S3.Quantum.Measurement.AntidistinguishabilityGram.hermitian_projection_complement_psd
    projection hproj.1 hproj.2.1
  have havg : ∀ k p ψ, IsDecomposition rho k p ψ →
      (∑ j, p j * quadratic (coherenceVector (ψ j))) = 2 / 3 := by
    intro k p ψ hd
    calc
      _ = ∑ j, p j * (2 / 3) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hp : p j = 0
        · rw [hp, zero_mul, zero_mul]
        · rw [unit_span_value (ψ j) (hd.2.2.1 j)
            (decomposition_support rho (1 - projection) p ψ hd hq hproj.2.2 j
              (lt_of_le_of_ne (hd.1 j) (Ne.symm hp)))]
      _ = 2 / 3 := by rw [← Finset.sum_mul, hd.2.1, one_mul]
  ext x
  constructor
  · rintro ⟨k, p, ψ, hd, rfl⟩
    exact Set.mem_singleton_iff.mpr (havg k p ψ hd)
  · intro hx
    refine ⟨2, (fun _ => 1 / 2), ![v, w], witness_decomposition, ?_⟩
    exact (Set.mem_singleton_iff.mp hx).trans (havg _ _ _ witness_decomposition).symm

private lemma witness_mixed : IsMixed rho := by
  sorry

theorem result : ¬ claim := by
  intro h
  have hlt := h 4 quadratic quadratic_coherence quadratic_nonzero rho witness_mixed
  change sInf (decompositionValues quadratic rho) < sSup (decompositionValues quadratic rho) at hlt
  rw [values_singleton, csInf_singleton, csSup_singleton] at hlt
  exact (lt_irrefl _ hlt)

end D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality
