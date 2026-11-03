/- GID: D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/CoolingMapThermalOperationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.claim; result=D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.result; claim=D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.claim
   digest: A four-level cooling transition excludes every finite ground-space thermal operation. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.SLDSpectralEnergy
import Mathlib.LinearAlgebra.Matrix.UnitaryGroup

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.SLDSpectralEnergy

namespace D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation

/-- A source cooling Kraus operator in increasing energy order. -/
def IsCoolingKraus {d : ℕ} (K : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  K.IsDiag ∨ ∃ j k : Fin d, j < k ∧ ∃ c : ℂ, K = c • Matrix.single j k 1

/-- Feasibility of a transition through a finite cooling Kraus channel. -/
def IsCoolingMap {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (n : ℕ) (K : Fin n → Matrix (Fin d) (Fin d) ℂ),
    (∀ i, IsCoolingKraus (K i)) ∧ (∑ i, (K i)ᴴ * K i) = 1 ∧
      MatrixMap.of_kraus K K ρ = σ

/-- All coordinates attaining the least ancilla energy, including degeneracy. -/
def groundSet {m : ℕ} (e : Fin m → ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun a => ∀ b, e a ≤ e b)

/-- The normalized projector onto the full ancilla ground eigenspace. -/
def groundState {m : ℕ} (e : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  diagonal (fun a => if a ∈ groundSet e then ((groundSet e).card : ℂ)⁻¹ else 0)

/-- Commutation with the diagonal total Hamiltonian. -/
def IsEnergyConserving {d m : ℕ} (E : Fin d → ℝ) (e : Fin m → ℝ)
    (U : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ) : Prop :=
  U * diagonal (fun x => ((E x.1 + e x.2 : ℝ) : ℂ)) =
    diagonal (fun x => ((E x.1 + e x.2 : ℝ) : ℂ)) * U

/-- The paper's idealized low-temperature thermal output. -/
def thermalOutput {d m : ℕ} (e : Fin m → ℝ)
    (U : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  partialTraceRight (U * Matrix.kronecker ρ (groundState e) * Uᴴ)

/-- Conjecture 1 under the preregistered finite ground-space reading. -/
def claim : Prop :=
  ∀ (d : ℕ) (E : Fin d → ℝ), StrictMono E →
    (∀ i j k l : Fin d, i < j → k < l → E j - E i = E l - E k →
      i = k ∧ j = l) →
    ∀ ρ σ : Matrix (Fin d) (Fin d) ℂ, IsDensity ρ → IsDensity σ →
      IsCoolingMap ρ σ →
      ∃ (m : ℕ) (e : Fin m → ℝ) (U : Matrix.unitaryGroup (Fin d × Fin m) ℂ),
        0 < m ∧ IsEnergyConserving E e U ∧ thermalOutput e U ρ = σ

private def levels : Fin 4 → ℝ := ![0, 1, 3, 7]

private def rho : Matrix (Fin 4) (Fin 4) ℂ := fun _ _ => 1 / 4

private def factor : Matrix (Fin 4) (Fin 2) ℂ :=
  !![1, 0; 0, 1; 3 / 5, 4 / 5; 3 / 5, 4 * Complex.I / 5]

private def sigma : Matrix (Fin 4) (Fin 4) ℂ := (1 / 4 : ℝ) • (factor * factorᴴ)

private def kraus : Fin 2 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![diagonal ![1, 0, 3 / 5, 3 / 5],
    diagonal ![0, 1, 4 / 5, 4 * Complex.I / 5]]

private lemma levels_valid : StrictMono levels ∧
    (∀ i j k l : Fin 4, i < j → k < l → levels j - levels i = levels l - levels k →
      i = k ∧ j = l) := by
  sorry

private lemma kraus_complete : (∑ i, (kraus i)ᴴ * kraus i) = 1 := by
  sorry

private lemma instance_density : IsDensity rho ∧ IsDensity sigma := by
  sorry

private lemma instance_cooling : IsCoolingMap rho sigma := by
  sorry

private lemma sigma_diagonal (j : Fin 4) : sigma j j = 1 / 4 := by
  sorry

private lemma ground_nonempty {m : ℕ} (hm : 0 < m) (e : Fin m → ℝ) :
    (groundSet e).Nonempty := by
  sorry

private lemma energy_entry {d m : ℕ} (E : Fin d → ℝ) (e : Fin m → ℝ)
    (U : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ)
    (h : IsEnergyConserving E e U) (j k : Fin d) (a b : Fin m)
    (hE : E j + e b ≠ E k + e a) : U (j, b) (k, a) = 0 := by
  sorry

private lemma energy_downward {d m : ℕ} (E : Fin d → ℝ) (hE : StrictMono E)
    (e : Fin m → ℝ) (U : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ)
    (h : IsEnergyConserving E e U) (j k : Fin d) (a b : Fin m)
    (ha : a ∈ groundSet e) (hjk : k < j) : U (j, b) (k, a) = 0 := by
  sorry

private lemma thermal_populations {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix (Fin 4 × Fin m) (Fin 4 × Fin m) ℂ)
    (h : IsEnergyConserving levels e U) (j : Fin 4) :
    (thermalOutput e U rho j j).re =
      (1 / (4 * (groundSet e).card : ℝ)) *
        ∑ k : Fin 4, ∑ a ∈ groundSet e, ∑ b : Fin m, Complex.normSq (U (j, b) (k, a)) := by
  sorry

private lemma population_support {m : ℕ} (hm : 0 < m) (e : Fin m → ℝ)
    (U : Matrix.unitaryGroup (Fin 4 × Fin m) ℂ)
    (h : IsEnergyConserving levels e U) (hout : thermalOutput e U rho = sigma) :
    ∀ (j k : Fin 4) (a b : Fin m), a ∈ groundSet e →
      (j ≠ k ∨ b ∉ groundSet e) → (U : Matrix _ _ ℂ) (j, b) (k, a) = 0 := by
  have hp := thermal_populations e U h
  have hd := energy_downward levels levels_valid.1 e U h
  have hs := sigma_diagonal
  have hg := ground_nonempty hm e
  sorry

private def block {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix (Fin 4 × Fin m) (Fin 4 × Fin m) ℂ) (k : Fin 4) :
    Matrix {a // a ∈ groundSet e} {a // a ∈ groundSet e} ℂ :=
  fun b a => U (k, b.1) (k, a.1)

private lemma block_unitary {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix.unitaryGroup (Fin 4 × Fin m) ℂ)
    (hs : ∀ (j k : Fin 4) (a b : Fin m), a ∈ groundSet e →
      (j ≠ k ∨ b ∉ groundSet e) → (U : Matrix _ _ ℂ) (j, b) (k, a) = 0)
    (k : Fin 4) : block e U k ∈ Matrix.unitaryGroup _ ℂ := by
  sorry

private lemma block_coherences {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix (Fin 4 × Fin m) (Fin 4 × Fin m) ℂ)
    (hs : ∀ (j k : Fin 4) (a b : Fin m), a ∈ groundSet e →
      (j ≠ k ∨ b ∉ groundSet e) → U (j, b) (k, a) = 0)
    (hout : thermalOutput e U rho = sigma) (i j : Fin 4) :
    trace (block e U i * (block e U j)ᴴ) =
      ((groundSet e).card : ℂ) * (factor * factorᴴ) i j := by
  sorry

private lemma gram_null {n : Type*} [Fintype n] [DecidableEq n]
    (A : Fin 4 → Matrix n n ℂ)
    (h : ∀ i j, trace (A i * (A j)ᴴ) = (Fintype.card n : ℂ) * (factor * factorᴴ) i j) :
    A 2 = (3 / 5 : ℂ) • A 0 + (4 / 5 : ℂ) • A 1 ∧
      A 3 = (3 / 5 : ℂ) • A 0 + (4 * Complex.I / 5 : ℂ) • A 1 := by
  sorry

private lemma unitary_obstruction {n : Type*} [Fintype n] [DecidableEq n]
    (hn : Nonempty n) (A : Fin 4 → Matrix n n ℂ)
    (hU : ∀ k, A k ∈ Matrix.unitaryGroup n ℂ)
    (h2 : A 2 = (3 / 5 : ℂ) • A 0 + (4 / 5 : ℂ) • A 1)
    (h3 : A 3 = (3 / 5 : ℂ) • A 0 + (4 * Complex.I / 5 : ℂ) • A 1) : False := by
  sorry

private lemma thermal_impossible {m : ℕ} (hm : 0 < m) (e : Fin m → ℝ)
    (U : Matrix.unitaryGroup (Fin 4 × Fin m) ℂ)
    (h : IsEnergyConserving levels e U) (hout : thermalOutput e U rho = sigma) : False := by
  have hs := population_support hm e U h hout
  have hU := block_unitary e U hs
  have hG := block_coherences e U hs hout
  obtain ⟨h2, h3⟩ := gram_null (block e U) hG
  obtain ⟨a, ha⟩ := ground_nonempty hm e
  exact unitary_obstruction ⟨⟨a, ha⟩⟩ (block e U) hU h2 h3

theorem result : ¬ claim := by
  intro h
  obtain ⟨m, e, U, hm, hE, hout⟩ :=
    h 4 levels levels_valid.1 levels_valid.2 rho sigma
      instance_density.1 instance_density.2 instance_cooling
  exact thermal_impossible hm e U hE hout

end D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation
