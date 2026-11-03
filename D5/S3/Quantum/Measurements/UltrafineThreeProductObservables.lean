/- GID: D5/S3/Quantum/Measurements/UltrafineThreeProductObservables
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/UltrafineThreeProductObservables
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Three product observables have useless pairs and a useful triple. -/

import D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
import D5.S3.Quantum.PureState.PureStateHandshake

open Matrix Finset
open scoped ComplexOrder Kronecker
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation (IsDensity)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

namespace D5.S3.Quantum.Measurements.UltrafineThreeProductObservables
noncomputable section
set_option autoImplicit false

/-- The convex hull of unit pure product projectors. -/
def IsSeparable {m n : ℕ}
    (σ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : Prop :=
  σ ∈ convexHull ℝ {τ | ∃ (a : Fin m → ℂ) (b : Fin n → ℂ),
    star a ⬝ᵥ a = 1 ∧ star b ⬝ᵥ b = 1 ∧
      τ = rankOneDensity (fun p : Fin m × Fin n => a p.1 * b p.2)}

/-- Every joint expectation in the family is realised by a separable density matrix. -/
def IsUseless {d : ℕ} {ι : Type*}
    (obs : ι → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (s : Finset ι) : Prop :=
  ∀ ρ, IsDensity ρ → ∃ σ, IsDensity σ ∧ IsSeparable σ ∧
    ∀ i ∈ s, trace (σ * obs i) = trace (ρ * obs i)

/-- The three-observable existence question of Gachechiladze--Wyderka--Gühne. -/
def claim : Prop :=
  ∃ a b : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ,
    (∀ i, (a i).IsHermitian ∧ (b i).IsHermitian) ∧
    (∀ i j, i ≠ j → IsUseless (fun k => a k ⊗ₖ b k) {i, j}) ∧
    ¬ IsUseless (fun k => a k ⊗ₖ b k) univ

private def alice : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![1,0,0; 0,1,0; 0,0,1/100],
    !![0,1,0; 1,0,0; 0,0,1/100],
    !![1,0,0; 0,-1,0; 0,0,1/100]]

private def bob : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![2,1,0; 1,2,1; 0,1,2],
    !![1,0,0; 0,2,0; 0,0,3],
    !![1,0,0; 0,4,0; 0,0,9]]

private def obs (i : Fin 3) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  alice i ⊗ₖ bob i

private def hamiltonian : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  obs 0 + obs 1 + obs 2

private lemma factors_hermitian (i : Fin 3) :
    (alice i).IsHermitian ∧ (bob i).IsHermitian := by
  sorry

private lemma diagonal_family_useless {d : ℕ} {ι : Type*}
    (a b : ι → Matrix (Fin d) (Fin d) ℂ) (s : Finset ι)
    (u : Matrix.unitaryGroup (Fin d) ℂ)
    (hdiag : (∀ i ∈ s, (star (u : Matrix (Fin d) (Fin d) ℂ) * a i * u).IsDiag) ∨
      (∀ i ∈ s, (star (u : Matrix (Fin d) (Fin d) ℂ) * b i * u).IsDiag)) :
    IsUseless (fun i => a i ⊗ₖ b i) s := by
  sorry

private lemma pairs_useless (i j : Fin 3) (hij : i ≠ j) : IsUseless obs {i, j} := by
  sorry

private lemma hamiltonian_hermitian : hamiltonian.IsHermitian := by
  sorry

private lemma ground_state :
    ∃ (λ : ℝ) (g : Fin 3 × Fin 3 → ℂ),
      λ < 0 ∧ star g ⬝ᵥ g = 1 ∧
      hamiltonian *ᵥ g = (λ : ℂ) • g ∧
      (hamiltonian - (λ : ℂ) • 1).PosSemidef := by
  sorry

private lemma no_product_ground (λ : ℝ) (hλ : λ < 0)
    (a b : Fin 3 → ℂ) (ha : star a ⬝ᵥ a = 1) (hb : star b ⬝ᵥ b = 1) :
    hamiltonian *ᵥ (fun p : Fin 3 × Fin 3 => a p.1 * b p.2) ≠
      (λ : ℂ) • (fun p : Fin 3 × Fin 3 => a p.1 * b p.2) := by
  sorry

private lemma separable_ground_exclusion
    (λ : ℝ) (hpos : (hamiltonian - (λ : ℂ) • 1).PosSemidef)
    (hnoprod : ∀ (a b : Fin 3 → ℂ), star a ⬝ᵥ a = 1 → star b ⬝ᵥ b = 1 →
      hamiltonian *ᵥ (fun p : Fin 3 × Fin 3 => a p.1 * b p.2) ≠
        (λ : ℂ) • (fun p : Fin 3 × Fin 3 => a p.1 * b p.2))
    (σ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hσ : IsSeparable σ) :
    λ < (trace (σ * hamiltonian)).re := by
  sorry

private lemma triple_useful : ¬ IsUseless obs univ := by
  obtain ⟨λ, g, hλ, hg, heig, hpos⟩ := ground_state
  have hρ : IsDensity (rankOneDensity g) := by
    refine ⟨posSemidef_vecMulVec_self_star g, ?_⟩
    simpa only [rankOneDensity, trace_vecMulVec, dotProduct_comm] using hg
  intro huseless
  obtain ⟨σ, _, hσ, hmatch⟩ := huseless (rankOneDensity g) hρ
  have henergy : trace (σ * hamiltonian) = (λ : ℂ) := by
    have h0 := hmatch 0 (mem_univ 0)
    have h1 := hmatch 1 (mem_univ 1)
    have h2 := hmatch 2 (mem_univ 2)
    change trace (σ * (obs 0 + obs 1 + obs 2)) = _
    rw [mul_add, mul_add, trace_add, trace_add, h0, h1, h2,
      ← trace_add, ← trace_add, ← mul_add, ← mul_add]
    change trace (rankOneDensity g * hamiltonian) = _
    rw [trace_mul_comm, rankOneDensity, mul_vecMulVec, trace_vecMulVec,
      heig, dotProduct_smul, dotProduct_comm, hg, smul_eq_mul, mul_one]
  have hstrict := separable_ground_exclusion λ hpos (no_product_ground λ hλ) σ hσ
  rw [henergy] at hstrict
  exact (lt_irrefl λ) hstrict

/-- Every pair is useless, whereas the full triple detects entanglement. -/
theorem result : claim := by
  exact ⟨alice, bob, factors_hermitian, pairs_useless, triple_useful⟩

end D5.S3.Quantum.Measurements.UltrafineThreeProductObservables
