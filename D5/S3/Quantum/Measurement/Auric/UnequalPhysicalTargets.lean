/- GID: D5/S3/Quantum/Measurement/Auric/UnequalPhysicalTargets
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/UnequalPhysicalTargets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The fixed labeled law and certificate predicates for sharp coherent record information. -/

import D5.S3.Quantum.Measurement.Auric.ProjectiveRecord
import D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
import D5.S3.Quantum.Measurement.Auric.EqualBlockProjection
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! Exact theorem types and the information-theoretic transfer for the fixed-law budget. -/

namespace D5.S3.Quantum.Measurement.Auric

open _root_.Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Measurement.Auric.CoordinatePinching
open D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
open D5.S3.Quantum.Measurement.Auric.EqualBlockEffects (entropyIntegrand)
open D5.S3.Quantum.Measurement.Auric.EqualBlockProjection (gain)
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching (vonNeumannEntropy)

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def capacity (c : ι → Fin 3) (j : Fin 3) : ℕ :=
  Fintype.card {a : ι // c a = j}

def FlatAtTrace (c : ι → Fin 3) (r : ℕ) (s : Fin 3 → ℝ)
    (P : Matrix ι ι ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P ∧ P.rank = r ∧
    (∀ j, (((coordinatePVM c).proj j * P).trace).re = s j) ∧
    ∀ a, (P a a).re = s (c a) / (capacity c (c a) : ℝ)

def InputAtLaw (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ)
    (ρ : DensityState ι) : Prop :=
  ∃ P : Matrix ι ι ℂ, FlatAtTrace c r (fun j => (r : ℝ) * q j) P ∧
    CStarMatrix.ofMatrix.symm ρ.1 = ((r : ℂ)⁻¹) • P

def FeasibleLaw (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ) : Prop :=
  (∀ j, 0 ≤ q j ∧ (r : ℝ) * q j ≤ (capacity c j : ℝ)) ∧ ∑ j, q j = 1

def effectValues (flip : Bool) (d : ℕ) (m : Fin 3 → ℕ) (t : Fin 3 → ℝ) :
    Set ℝ :=
  {v | ∃ A : Fin 3 → Matrix (Fin d) (Fin d) ℂ, ∃ hA : Feasible m t A,
    spectralSum (entropyIntegrand flip) A hA.1 = v}

def gainValues (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ) : Set ℝ :=
  {v | ∃ ρ : DensityState ι, InputAtLaw c r q ρ ∧ gain c ρ = v}

def recordConditionalEntropy (c : ι → Fin 3) (ρ : DensityState ι) : ℝ :=
  vonNeumannEntropy (recordedState (coordinatePVM c) ρ) -
    vonNeumannEntropy (marginalRight (recordedState (coordinatePVM c) ρ))

/-- State and optimize the two possible frame factorizations with the same range theorem.
The final theorem uses the smaller dimension, with the direct branch at a tie. -/
def GeometryStatement (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ) : Prop :=
  0 < r → r ≤ Fintype.card ι →
    ∀ flip : Bool,
      let d := if flip then Fintype.card ι - r else r
      let t := fun j =>
        if flip then (capacity c j : ℝ) - (r : ℝ) * q j else (r : ℝ) * q j
      gainValues c r q = (fun x : ℝ => x / r) '' effectValues flip d (capacity c) t

def binaryTerm (m : ℕ) (t : ℝ) : ℝ :=
  (m : ℝ) * Real.binEntropy (t / (m : ℝ))

/-- The missing-deficit branch supplies both objectives under the same explicit cap pattern. -/
def DisjointEffectsStatement (d : ℕ) (m : Fin 3 → ℕ) (t : Fin 3 → ℝ) : Prop :=
  ∀ i k a : Fin 3, i ≠ k → i ≠ a → k ≠ a →
    d ≤ m a → m i + m k ≤ d →
    (∀ j, 0 ≤ t j ∧ t j ≤ (m j : ℝ)) → (∑ j, t j) = (d : ℝ) →
    ∀ flip : Bool, IsGreatest (effectValues flip d m t)
      (binaryTerm (m i) (t i) + binaryTerm (m k) (t k))

/-- The same admissible density state realizes all three extrema. -/
def SharpRecordBudget (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ) (B : ℝ) : Prop :=
  let H := ∑ j, Real.negMulLog (q j)
  ∃ ρ : DensityState ι, InputAtLaw c r q ρ ∧
    gain c ρ = B / (r : ℝ) ∧
    quantumMutualInformation (recordedState (coordinatePVM c) ρ) = H + B / (r : ℝ) ∧
    recordConditionalEntropy c ρ = -(B / (r : ℝ)) ∧
    ∀ σ : DensityState ι, InputAtLaw c r q σ →
      gain c σ ≤ B / (r : ℝ) ∧
      quantumMutualInformation (recordedState (coordinatePVM c) σ) ≤ H + B / (r : ℝ) ∧
      -(B / (r : ℝ)) ≤ recordConditionalEntropy c σ

/-- Certificate values for the disjoint, boundary, and strict trace cases. -/
def SpectralBudgetCertificate (flip : Bool) (d : ℕ) (m : Fin 3 → ℕ)
    (t : Fin 3 → ℝ) (B : ℝ) : Prop :=
  let l : Fin 3 → ℕ := fun j => d - m j
  let b := d - ∑ j, l j
  (d = 0 ∧ B = 0) ∨
  (0 < d ∧ d < (∑ j, l j) ∧
    ∃ a i k : Fin 3, a ≠ i ∧ a ≠ k ∧ i ≠ k ∧
      d ≤ m a ∧ m i + m k < d ∧ B = binaryTerm (m i) (t i) + binaryTerm (m k) (t k)) ∨
  (0 < d ∧ (∑ j, l j) ≤ d ∧
    ((∃ j i : Fin 3, j ≠ i ∧ t j = (min d (m j) : ℝ) ∧
        B = binaryTerm (l j) (t i)) ∨
     (∃ j i k : Fin 3, j ≠ i ∧ j ≠ k ∧ i ≠ k ∧ t j = 0 ∧
        B = binaryTerm (d - l i - l k) (t i - (l k : ℝ))) ∨
     ((∀ j, 0 < t j ∧ t j < (min d (m j) : ℝ)) ∧
       if flip then
         ∃ (w : Fin 3 → ℝ) (k : Fin 4 → ℝ), (∀ j, 0 < w j) ∧ (∀ c, 0 < k c) ∧
           (∀ c, ∑ j, allocation (complementEntries w k) j c = 1) ∧
           (∀ j, (∑ c, (multiplicity l b c : ℝ) *
             allocation (complementEntries w k) j c) = t j) ∧
           B = allocationValue (entropyIntegrand true) l b (complementEntries w k)
       else
         ∃ w : Fin 3 → ℝ, (∀ j, 0 < w j) ∧ (∑ j, w j) = 1 ∧
           (∀ j, weightMass l b w j = t j) ∧
           B = allocationValue (entropyIntegrand false) l b (weightEntries w))))

/-- Complete target for the fixed three-label PVM. Any valid certificate gives
the same value and the same three extremum statements. -/
def CompleteBudgetStatement (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ) : Prop :=
  0 < r → r ≤ Fintype.card ι →
    ((∃ ρ : DensityState ι, InputAtLaw c r q ρ) ↔ FeasibleLaw c r q) ∧
    (FeasibleLaw c r q →
      let flip := decide (Fintype.card ι - r < r)
      let d := if flip then Fintype.card ι - r else r
      let t := fun j =>
        if flip then (capacity c j : ℝ) - (r : ℝ) * q j else (r : ℝ) * q j
      (∃ B, SpectralBudgetCertificate flip d (capacity c) t B) ∧
      ∀ B, SpectralBudgetCertificate flip d (capacity c) t B → SharpRecordBudget c r q B)

theorem input_recordLaw {c : ι → Fin 3} {r : ℕ} (hr : 0 < r)
    {q : Fin 3 → ℝ} {ρ : DensityState ι} (hρ : InputAtLaw c r q ρ) :
    recordLaw (coordinatePVM c) ρ = q := by
  obtain ⟨P, hP, hM⟩ := hρ
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  funext j
  rw [recordLaw, hM, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hP.2.2.2.1]
  exact inv_mul_cancel_left₀ hr' (q j)

/-- Transfer a sharp geometry answer through the actual coherent recording. -/
theorem physical_of_gain (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ) (B : ℝ)
    (hr : 0 < r)
    (hOpt : IsGreatest (gainValues c r q) (B / (r : ℝ))) :
    SharpRecordBudget c r q B := by
  obtain ⟨ρ, hρ, hgain⟩ := hOpt.1
  obtain ⟨hi, hc⟩ := projective_record_information (coordinatePVM c) ρ
  rw [input_recordLaw hr hρ] at hi
  change gain c ρ = B / (r : ℝ) at hgain
  change quantumMutualInformation (recordedState (coordinatePVM c) ρ) =
    gain c ρ + ∑ j, Real.negMulLog (q j) at hi
  change recordConditionalEntropy c ρ = -gain c ρ at hc
  refine ⟨ρ, hρ, hgain, ?_, hc.trans (congrArg Neg.neg hgain), ?_⟩
  · rw [hi, hgain, add_comm]
  · intro σ hσ
    have hle := hOpt.2 (show gain c σ ∈ gainValues c r q from ⟨σ, hσ, rfl⟩)
    obtain ⟨hi', hc'⟩ := projective_record_information (coordinatePVM c) σ
    rw [input_recordLaw hr hσ] at hi'
    change quantumMutualInformation (recordedState (coordinatePVM c) σ) =
      gain c σ + ∑ j, Real.negMulLog (q j) at hi'
    change recordConditionalEntropy c σ = -gain c σ at hc'
    exact ⟨hle, by rw [hi', add_comm]; exact add_le_add le_rfl hle,
      by rw [hc']; exact neg_le_neg hle⟩

end

end D5.S3.Quantum.Measurement.Auric

