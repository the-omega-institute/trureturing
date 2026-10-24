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

private lemma mixed_CAR {N : ℕ} (i j : Fin N) :
    fullC i * (fullC j)ᴴ + (fullC j)ᴴ * fullC i =
      if i = j then (1 : FullOperator N) else 0 := by
  by_cases h : i = j
  · subst j
    simpa using fullC_CAR i
  · rw [if_neg h]
    rcases lt_or_gt_of_ne h with h | h
    · exact fullC_mixed_anticomm_of_lt i j h
    · have ht := congrArg Matrix.conjTranspose (fullC_mixed_anticomm_of_lt j i h)
      simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero, add_comm] using ht

private lemma creation_anticomm {N : ℕ} (i j : Fin N) :
    (fullC i)ᴴ * (fullC j)ᴴ + (fullC j)ᴴ * (fullC i)ᴴ = 0 := by
  let g := D5.S3.Quantum.Fermionic.FockMajoranaCarrier.majorana (N := N)
  have hc := (majorana_clifford_and_parity N).2.2.2.1
  have h00 := hc (i, false) (j, false)
  have h11 := hc (i, true) (j, true)
  have h01 := hc (i, false) (j, true)
  have h10 := hc (i, true) (j, false)
  have hz : (4 : ℂ) • ((fullC i)ᴴ * (fullC j)ᴴ + (fullC j)ᴴ * (fullC i)ᴴ) = 0 := by
    calc
      _ = (g i false * g j false + g j false * g i false) -
          (g i true * g j true + g j true * g i true) +
          Complex.I • ((g i false * g j true + g j true * g i false) +
            (g i true * g j false + g j false * g i true)) := by
        dsimp [g, D5.S3.Quantum.Fermionic.FockMajoranaCarrier.majorana]
        simp only [mul_add, add_mul, mul_sub, sub_mul, Matrix.smul_mul, Matrix.mul_smul,
          smul_add, smul_sub, smul_smul, Complex.I_mul_I]
        ext s t
        simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      _ = 0 := by
        change (_ - _ + Complex.I • (_ + _)) = 0
        rw [h00, h11, h01, h10]
        simp
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

private lemma quadratic_commutator {N : ℕ} (J μ : ℝ) (j : Fin N) :
    hamiltonian N J μ * (fullC j)ᴴ - (fullC j)ᴴ * hamiltonian N J μ =
      ∑ i : Fin N, hopping N J μ i j • (fullC i)ᴴ := by
  have hterm (i k : Fin N) :
      ((fullC i)ᴴ * fullC k) * (fullC j)ᴴ -
          (fullC j)ᴴ * ((fullC i)ᴴ * fullC k) =
        if k = j then (fullC i)ᴴ else 0 := by
    calc
      _ = (fullC i)ᴴ * (fullC k * (fullC j)ᴴ + (fullC j)ᴴ * fullC k) -
          ((fullC i)ᴴ * (fullC j)ᴴ + (fullC j)ᴴ * (fullC i)ᴴ) * fullC k := by
        noncomm_ring
      _ = _ := by rw [mixed_CAR, creation_anticomm]; split_ifs <;> simp
  unfold hamiltonian
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, hterm]
  simp

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
  let K := ((t : ℂ) * Complex.I) • hamiltonian N J μ
  have hinv : NormedSpace.exp (-K) * NormedSpace.exp K = 1 := by
    rw [← Matrix.exp_add_of_commute (-K) K (Commute.refl K).neg_left]
    simp
  unfold evolve
  change NormedSpace.exp K * (A * B) * NormedSpace.exp (-K) = _
  calc
    _ = NormedSpace.exp K * A * (NormedSpace.exp (-K) * NormedSpace.exp K) * B *
        NormedSpace.exp (-K) := by rw [hinv]; simp only [mul_one, mul_assoc]
    _ = _ := by simp only [K, mul_assoc]

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
