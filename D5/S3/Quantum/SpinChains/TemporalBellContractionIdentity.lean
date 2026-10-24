/- GID: D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/TemporalBellContractionIdentity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Temporal Bell endpoint contractions equal one-particle propagator entries for every N. -/

import D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression
import D5.S3.Quantum.Fermionic.FockMajoranaCarrier
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-! Endpoint vacuum contractions for the open XX chain in the Heisenberg picture. -/

open Matrix
open scoped BigOperators Matrix ComplexConjugate
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression (fullC_entry)
open D5.S3.Quantum.Fermionic.FockMajoranaCarrier (numberParity majorana_clifford_and_parity)
open PredictiveThermodynamic.Physical (Assignment)

noncomputable section
namespace D5.S3.Quantum.SpinChains.TemporalBellContractionIdentity

def hopping (N : ℕ) (J μ : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i = j then -(μ : ℂ)
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -(J : ℂ) else 0

def hamiltonian (N : ℕ) (J μ : ℝ) : FullOperator N :=
  ∑ i : Fin N, ∑ j : Fin N, hopping N J μ i j • ((fullC i)ᴴ * fullC j)

def propagator (N : ℕ) (J μ t : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  NormedSpace.exp (((t : ℂ) * Complex.I) • hopping N J μ)

def evolve {N : ℕ} (J μ t : ℝ) (A : FullOperator N) : FullOperator N :=
  NormedSpace.exp (((t : ℂ) * Complex.I) • hamiltonian N J μ) * A *
    NormedSpace.exp (-(((t : ℂ) * Complex.I) • hamiltonian N J μ))

def sigmaXLast (N : ℕ) (hN : 0 < N) : FullOperator N :=
  (((List.finRange N).filter (fun j => j.val < N - 1)).map
    (fun j => (1 : FullOperator N) - (2 : ℂ) • ((fullC j)ᴴ * fullC j))).prod *
      ((fullC ⟨N - 1, Nat.sub_lt hN (by decide)⟩)ᴴ +
        fullC ⟨N - 1, Nat.sub_lt hN (by decide)⟩)

def vacuumIndex (N : ℕ) : Assignment N := fun _ => false

def claim : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N) (J μ t : ℝ),
    let first : Fin N := ⟨0, by omega⟩
    let last : Fin N := ⟨N - 1, by omega⟩
    let X := evolve J μ t (sigmaXLast N (by omega))
    ((fullC last * fullC first * X * (fullC first)ᴴ)
        (vacuumIndex N) (vacuumIndex N) +
      (fullC last * fullC first * X * (fullC last)ᴴ)
        (vacuumIndex N) (vacuumIndex N)).re =
      (propagator N J μ t last last - propagator N J μ t first last).re

private lemma quadratic_commutator {N : ℕ} (J μ : ℝ) (j : Fin N) :
    hamiltonian N J μ * (fullC j)ᴴ - (fullC j)ᴴ * hamiltonian N J μ =
      ∑ i : Fin N, hopping N J μ i j • (fullC i)ᴴ := by
  sorry

private lemma creation_evolution {N : ℕ} (J μ t : ℝ) (j : Fin N) :
    evolve J μ t (fullC j)ᴴ =
      ∑ i : Fin N, propagator N J μ t i j • (fullC i)ᴴ := by
  have hcomm := quadratic_commutator (N := N) J μ
  sorry

private lemma annihilation_evolution {N : ℕ} (J μ t : ℝ) (j : Fin N) :
    evolve J μ t (fullC j) =
      ∑ i : Fin N, star (propagator N J μ t i j) • fullC i := by
  have hcreate := creation_evolution J μ t j
  sorry

private lemma sigmaXLast_parity (N : ℕ) (hN : 0 < N) :
    sigmaXLast N hN = numberParity N *
      (fullC ⟨N - 1, Nat.sub_lt hN (by decide)⟩ -
        (fullC ⟨N - 1, Nat.sub_lt hN (by decide)⟩)ᴴ) := by
  sorry

private lemma parity_stationary (N : ℕ) (J μ t : ℝ) :
    evolve J μ t (numberParity N) = numberParity N := by
  sorry

private lemma evolve_mul {N : ℕ} (J μ t : ℝ) (A B : FullOperator N) :
    evolve J μ t (A * B) = evolve J μ t A * evolve J μ t B := by
  sorry

private lemma evolve_sub {N : ℕ} (J μ t : ℝ) (A B : FullOperator N) :
    evolve J μ t (A - B) = evolve J μ t A - evolve J μ t B := by
  unfold evolve
  noncomm_ring

private lemma evolved_endpoint (N : ℕ) (hN : 0 < N) (J μ t : ℝ) :
    evolve J μ t (sigmaXLast N hN) = numberParity N *
      ((∑ i : Fin N, star (propagator N J μ t i ⟨N - 1, by omega⟩) • fullC i) -
        ∑ i : Fin N, propagator N J μ t i ⟨N - 1, by omega⟩ • (fullC i)ᴴ) := by
  rw [sigmaXLast_parity, evolve_mul, parity_stationary, evolve_sub,
    annihilation_evolution, creation_evolution]

private lemma vacuum_contractions {N : ℕ} (a b : Fin N) (hab : a ≠ b)
    (u v : Fin N → ℂ) :
    (fullC b * fullC a *
        (numberParity N * ((∑ i : Fin N, u i • fullC i) -
          ∑ i : Fin N, v i • (fullC i)ᴴ)) * (fullC a)ᴴ)
        (vacuumIndex N) (vacuumIndex N) +
      (fullC b * fullC a *
        (numberParity N * ((∑ i : Fin N, u i • fullC i) -
          ∑ i : Fin N, v i • (fullC i)ᴴ)) * (fullC b)ᴴ)
        (vacuumIndex N) (vacuumIndex N) = v b - v a := by
  sorry

private lemma complex_identity (N : ℕ) (hN : 2 ≤ N) (J μ t : ℝ) :
    let first : Fin N := ⟨0, by omega⟩
    let last : Fin N := ⟨N - 1, by omega⟩
    let X := evolve J μ t (sigmaXLast N (by omega))
    (fullC last * fullC first * X * (fullC first)ᴴ)
        (vacuumIndex N) (vacuumIndex N) +
      (fullC last * fullC first * X * (fullC last)ᴴ)
        (vacuumIndex N) (vacuumIndex N) =
      propagator N J μ t last last - propagator N J μ t first last := by
  dsimp only
  rw [evolved_endpoint]
  apply vacuum_contractions
  intro h
  have := congrArg Fin.val h
  dsimp at this
  omega

theorem result : claim := by
  intro N hN J μ t
  exact congrArg Complex.re (complex_identity N hN J μ t)

end D5.S3.Quantum.SpinChains.TemporalBellContractionIdentity
