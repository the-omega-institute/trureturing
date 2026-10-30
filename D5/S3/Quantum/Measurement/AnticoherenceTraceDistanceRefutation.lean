/- GID: D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.claim; result=D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.result; claim=D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.claim
   digest: A spin-four covariant channel lowers order-seven trace-distance anticoherence. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
import D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability

/-!
The mixed-state reading of axiom (T4) in Denis–Lacaille–Martin–Serrano-Ensástiga,
arXiv:2605.29436v1, with the witness specified in preregistration #24441.
Reduced states are expressed in the normalized Dicke basis. Their splitting
isometry implements the ordinary qubit partial trace in these coordinates.
-/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Measurement.AnticoherenceTraceDistanceRefutation

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (Jplus Jx Jy Jz)

/-- The tensor power in the computational basis of `n` qubits. -/
def qubitPower (n : ℕ) (u : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun x y => ∏ k, u (x k) (y k)

/-- The normalized Dicke embedding; the spin index counts qubits in state one. -/
def dickeIsometry (n : ℕ) : Matrix (Fin n → Fin 2) (Fin (n + 1)) ℂ :=
  fun x r => if (∑ k, (x k).val) = r.val then
    (Real.sqrt (n.choose r.val : ℝ) : ℂ)⁻¹ else 0

/-- The spin-`n/2` representation obtained by restricting the qubit tensor power. -/
def spinAction (n : ℕ) (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (dickeIsometry n)ᴴ * qubitPower n u.val * dickeIsometry n

/-- The Dicke splitting coefficients for the first `t` and last `n-t` qubits. -/
def dickeSplit (n t : ℕ) :
    Matrix (Fin (t + 1) × Fin (n - t + 1)) (Fin (n + 1)) ℂ :=
  fun kl r => if kl.1.val + kl.2.val = r.val then
    ((Real.sqrt ((t.choose kl.1.val : ℝ) * ((n - t).choose kl.2.val : ℝ)) /
      Real.sqrt (n.choose r.val : ℝ) : ℝ) : ℂ) else 0

/-- The qubit partial trace, expressed in the normalized `t`-qubit Dicke basis. -/
def reducedState {n : ℕ} (t : ℕ) (ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ :=
  partialTraceRight (dickeSplit n t * ρ * (dickeSplit n t)ᴴ)

/-- The maximally mixed state on the symmetric `t`-qubit subspace. -/
def mixedState (t : ℕ) : Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ :=
  (1 / ((t : ℂ) + 1)) • 1

/-- The source's maximum trace distance over all states of spin `t/2`. -/
def normalizer (t : ℕ) : ℝ :=
  sSup {d : ℝ | ∃ σ : Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ,
    σ.PosSemidef ∧ σ.trace = 1 ∧ d = traceNorm (σ - mixedState t)}

/-- The distance-based total anticoherence measure for Schatten exponent one. -/
def anticoherence {n : ℕ} (t : ℕ)
    (ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℝ :=
  1 - traceNorm (reducedState t ρ - mixedState t) / normalizer t

/-- Complete positivity, trace preservation, and covariance under every single-qubit SU(2). -/
def IsCovariantChannel {n : ℕ} (φ : MatrixMap (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop :=
  φ.IsCompletelyPositive ∧ φ.IsTracePreserving ∧
    ∀ (u : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      φ (spinAction n u * x * (spinAction n u)ᴴ) =
        spinAction n u * φ x * (spinAction n u)ᴴ

/-- Axiom (T4), including the source's full mixed-state range `1 ≤ t ≤ n`. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ t : ℕ, 1 ≤ t → t ≤ n →
    ∀ φ : MatrixMap (Fin (n + 1)) (Fin (n + 1)) ℂ, IsCovariantChannel φ →
    ∀ ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ρ.PosSemidef → ρ.trace = 1 → anticoherence t ρ ≤ anticoherence t (φ ρ)

private def witnessState : Matrix (Fin 9) (Fin 9) ℂ :=
  diagonal (fun r => (![209, 92, 560, 0, 441, 0, 294, 168, 0] r : ℂ) / 1764)

private def witnessKraus : Fin 5 → Matrix (Fin 9) (Fin 9) ℂ :=
  ![(1 / (Real.sqrt 1540 : ℂ)) • ((3 : ℂ) • (Jz 8 * Jz 8) - (20 : ℂ) • 1),
    (-(Real.sqrt (3 / 3080) : ℂ)) • (Jz 8 * Jplus 8 + Jplus 8 * Jz 8),
    (Real.sqrt (3 / 3080) : ℂ) • (Jz 8 * (Jplus 8)ᴴ + (Jplus 8)ᴴ * Jz 8),
    (Real.sqrt (3 / 3080) : ℂ) • (Jplus 8 * Jplus 8),
    (Real.sqrt (3 / 3080) : ℂ) • ((Jplus 8)ᴴ * (Jplus 8)ᴴ)]

private def witnessChannel : MatrixMap (Fin 9) (Fin 9) ℂ :=
  MatrixMap.of_kraus witnessKraus witnessKraus

private def quadrupole (a b : Fin 3) : Matrix (Fin 9) (Fin 9) ℂ :=
  let j : Fin 3 → Matrix (Fin 9) (Fin 9) ℂ := ![Jx 8, Jy 8, Jz 8]
  (1 / 2 : ℂ) • (j a * j b + j b * j a) -
    (if a = b then (20 / 3 : ℂ) else 0) • 1

private def witnessOutput : Matrix (Fin 9) (Fin 9) ℂ :=
  diagonal (fun r =>
    (![22288, 30100, 25528, 13149, 45540, 10584, 24654, 11613, 10584] r : ℂ) / 194040)

private lemma dicke_isometry (n : ℕ) : (dickeIsometry n)ᴴ * dickeIsometry n = 1 := by
  sorry

private lemma tensor_preserves_symmetric (n : ℕ)
    (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    qubitPower n u.val * dickeIsometry n = dickeIsometry n * spinAction n u := by
  sorry

private lemma dicke_split_partialTrace (t s : ℕ)
    (ρ : Matrix (Fin (t + s + 1)) (Fin (t + s + 1)) ℂ) :
    let v := dickeIsometry (t + s)
    let w := fun xy : (Fin t → Fin 2) × (Fin s → Fin 2) =>
      Fin.append xy.1 xy.2
    partialTraceRight ((v * ρ * vᴴ).submatrix w w) =
      dickeIsometry t * reducedState t ρ * (dickeIsometry t)ᴴ := by
  sorry

private lemma kraus_complete : ∑ q, (witnessKraus q)ᴴ * witnessKraus q = 1 := by
  sorry

private lemma cartesian_channel (x : Matrix (Fin 9) (Fin 9) ℂ) :
    witnessChannel x = (3 / 770 : ℂ) •
      ∑ a : Fin 3, ∑ b : Fin 3, quadrupole a b * x * quadrupole a b := by
  sorry

private lemma collective_rotation (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ r : Matrix (Fin 3) (Fin 3) ℝ, rᵀ * r = 1 ∧
      ∀ a : Fin 3,
        spinAction 8 u * (![Jx 8, Jy 8, Jz 8] a) * (spinAction 8 u)ᴴ =
          ∑ c : Fin 3, (r a c : ℂ) • (![Jx 8, Jy 8, Jz 8] c) := by
  sorry

private lemma channel_covariant (u : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (x : Matrix (Fin 9) (Fin 9) ℂ) :
    witnessChannel (spinAction 8 u * x * (spinAction 8 u)ᴴ) =
      spinAction 8 u * witnessChannel x * (spinAction 8 u)ᴴ := by
  sorry

private lemma witness_channel : IsCovariantChannel (n := 8) witnessChannel := by
  exact ⟨MatrixMap.of_kraus_isCompletelyPositive witnessKraus,
    MatrixMap.IsTracePreserving.of_kraus_isTracePreserving
      witnessKraus witnessKraus kraus_complete, channel_covariant⟩

private lemma witness_state : witnessState.PosSemidef ∧ witnessState.trace = 1 := by
  sorry

private lemma witness_output : witnessChannel witnessState = witnessOutput := by
  sorry

private lemma diagonal_reduction (n t : ℕ) (ht : t ≤ n) (p : Fin (n + 1) → ℝ) :
    reducedState t (diagonal (fun r => (p r : ℂ))) =
      diagonal (fun k => ((∑ r : Fin (n + 1), p r *
        (t.choose k.val : ℝ) * ((n - t).choose (r.val - k.val) : ℝ) /
        (n.choose r.val : ℝ) * (if k.val ≤ r.val then 1 else 0) : ℝ) : ℂ)) := by
  sorry

private lemma input_reduction : reducedState 7 witnessState =
    diagonal (fun k => (![21, 21, 40, 21, 21, 21, 21, 2] k : ℂ) / 168) := by
  sorry

private lemma output_reduction : reducedState 7 witnessOutput =
    diagonal (fun k =>
      (![69468, 87252, 64205, 82635, 78360, 59892, 43533, 32095] k : ℂ) / 517440) := by
  sorry

private lemma input_distance :
    traceNorm (reducedState 7 witnessState - mixedState 7) = 19 / 84 := by
  sorry

private lemma output_distance :
    traceNorm (reducedState 7 (witnessChannel witnessState) - mixedState 7) =
      3933 / 17248 := by
  sorry

private lemma normalizer_positive : 0 < normalizer 7 := by
  sorry

theorem result : ¬ claim := by
  intro h
  have hm := h 8 (by norm_num) 7 (by norm_num) (by norm_num)
    witnessChannel witness_channel witnessState witness_state.1 witness_state.2
  change 1 - traceNorm (reducedState 7 witnessState - mixedState 7) / normalizer 7 ≤
    1 - traceNorm (reducedState 7 (witnessChannel witnessState) - mixedState 7) /
      normalizer 7 at hm
  rw [input_distance, output_distance] at hm
  have hlt : (19 / 84 : ℝ) / normalizer 7 < (3933 / 17248 : ℝ) / normalizer 7 :=
    (div_lt_div_iff_of_pos_right normalizer_positive).2 (by norm_num)
  linarith

end D5.S3.Quantum.Measurement.AnticoherenceTraceDistanceRefutation
