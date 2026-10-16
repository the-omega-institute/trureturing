/- GID: D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.claim; result=D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.result; claim=D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.claim
   digest: Four qubit states admit adaptive query value 99/100 above pre-query bound 483/500. -/

import D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation

set_option linter.style.longLine false

namespace D5.S3.Quantum.Measurement.AdaptiveQueryQubitFourStateRefutation

open Matrix
open scoped BigOperators ComplexOrder

abbrev Q2 := D5.S3.Quantum.FiniteDimensional.QubitMatrix

/-- Nonnegative normalized priors and qubit density matrices. -/
def IsEnsemble {n : ℕ} (q : Fin n → ℝ) (ρ : Fin n → Q2) : Prop :=
  (∀ x, 0 ≤ q x) ∧ ∑ x, q x = 1 ∧
    ∀ x, (ρ x).PosSemidef ∧ trace (ρ x) = 1

/-- A finite positive operator-valued measure. -/
def IsPOVM {ι : Type} [Fintype ι] (M : ι → Q2) : Prop :=
  D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM M

private def cell {n : ℕ} (X : Finset (Fin n)) (ℓ : Fin 2) : Finset (Fin n) :=
  if ℓ = 0 then X else Xᶜ

/-- Each nonempty cell has its own normalized POVM; an empty cell contributes nothing. -/
def IsPreStrategy {n : ℕ} (X : Finset (Fin n)) (M : Fin 2 → Fin n → Q2) : Prop :=
  ∀ ℓ, (∀ x ∈ cell X ℓ, (M ℓ x).PosSemidef) ∧
    ((cell X ℓ).Nonempty → ∑ x ∈ cell X ℓ, M ℓ x = 1)

/-- The success value of a pre-measurement query, including its prior weights. -/
noncomputable def preValue {n : ℕ} (q : Fin n → ℝ) (ρ : Fin n → Q2)
    (X : Finset (Fin n)) (M : Fin 2 → Fin n → Q2) : ℝ :=
  ∑ ℓ, ∑ x ∈ cell X ℓ, q x * (trace (ρ x * M ℓ x)).re

/-- The supremum over all binary partitions and their cell measurements. -/
noncomputable def Ppre {n : ℕ} (q : Fin n → ℝ) (ρ : Fin n → Q2) : ℝ :=
  sSup {v | ∃ X M, IsPreStrategy X M ∧ v = preValue q ρ X M}

/-- The query and the two guesses can depend on the observed POVM outcome. -/
def IsAdaptiveStrategy {n m : ℕ} (M : Fin m → Q2)
    (P : Fin m → Finset (Fin n)) (f : Fin m → Fin 2 → Fin n) : Prop :=
  IsPOVM M ∧ ∀ z ℓ, f z ℓ ∈ cell (P z) ℓ

/-- The success value of an adaptive post-measurement query. -/
noncomputable def adaptiveValue {n m : ℕ} (q : Fin n → ℝ) (ρ : Fin n → Q2)
    (M : Fin m → Q2) (f : Fin m → Fin 2 → Fin n) : ℝ :=
  ∑ z, ∑ ℓ, q (f z ℓ) * (trace (ρ (f z ℓ) * M z)).re

/-- The proposed absence of adaptive advantage for every qubit ensemble of size at least four. -/
def claim : Prop :=
  ∀ (n : ℕ), 4 ≤ n → ∀ (q : Fin n → ℝ) (ρ : Fin n → Q2), IsEnsemble q ρ →
    ∀ (m : ℕ) (M : Fin m → Q2) (P : Fin m → Finset (Fin n))
      (f : Fin m → Fin 2 → Fin n), IsAdaptiveStrategy M P f →
        adaptiveValue q ρ M f ≤ Ppre q ρ

private noncomputable def q : Fin 4 → ℝ := ![33/100, 33/100, 33/100, 1/100]

private noncomputable def ket : Fin 4 → Fin 2 → ℂ :=
  ![![1, 0], ![1, 2], ![1, -2], ![1, 1]]

private noncomputable def weight : Fin 4 → ℝ := ![1, 1/5, 1/5, 1/2]

private noncomputable def rho (x : Fin 4) : Q2 :=
  weight x • vecMulVec (ket x) (star (ket x))

private theorem ensemble_valid : IsEnsemble q rho := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> norm_num [q]
  · norm_num [q, Fin.sum_univ_succ]
  · intro x
    constructor
    · exact (posSemidef_vecMulVec_self_star (ket x)).smul
        (by fin_cases x <;> norm_num [weight])
    · rw [rho, trace_smul, trace_vecMulVec]
      fin_cases x <;>
        norm_num [weight, ket, dotProduct, Fin.sum_univ_two, map_ofNat]

private noncomputable def effectKet : Fin 3 → Fin 2 → ℂ :=
  ![![0, 1], ![2, -1], ![2, 1]]

private noncomputable def effectWeight : Fin 3 → ℝ := ![3/4, 1/8, 1/8]

private noncomputable def effect (z : Fin 3) : Q2 :=
  effectWeight z • vecMulVec (effectKet z) (star (effectKet z))

private def partition : Fin 3 → Finset (Fin 4) := ![{1}, {0}, {0}]

private def guess : Fin 3 → Fin 2 → Fin 4 := ![![1, 2], ![0, 2], ![0, 1]]

private theorem adaptive_valid : IsAdaptiveStrategy effect partition guess := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z
    exact (posSemidef_vecMulVec_self_star (effectKet z)).smul
      (by fin_cases z <;> norm_num [effectWeight])
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [effect, effectWeight, effectKet, vecMulVec, Fin.sum_univ_succ,
        Matrix.sum_apply, Matrix.smul_apply, map_ofNat]
  · intro z ℓ
    fin_cases z <;> fin_cases ℓ <;> decide

private theorem adaptive_value : adaptiveValue q rho effect guess = 99/100 := by
  norm_num [adaptiveValue, q, rho, weight, ket, effect, effectWeight, effectKet,
    guess, trace, Matrix.mul_apply, vecMulVec, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.smul_apply, Complex.mul_re, Complex.mul_im, Matrix.cons_val_two,
    Matrix.cons_val_three, map_ofNat]

end D5.S3.Quantum.Measurement.AdaptiveQueryQubitFourStateRefutation
