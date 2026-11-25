/- GID: D5/S3/Quantum/Measurement/Auric/ProjectiveRecord
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/ProjectiveRecord
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The coherent recording of a complete PVM has the pinched system marginal, the original record law, and exact joint entropy identities. -/

import D5.S3.Quantum.Measurement.Auric.ProjectionSpectralTransport
import D5.S3.Quantum.Decoherence.NonselectiveMarginalization
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Measurement.Auric.CoordinatePinching

/-! A complete finite PVM defines a coherent joint state on the system and its record. -/

namespace D5.S3.Quantum.Measurement.Auric

open _root_.Matrix
open scoped Matrix BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)
open D5.S3.Quantum.Decoherence.RecordingIsometry
open D5.S3.Quantum.Decoherence.NonselectiveMarginalization
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Measurement.Auric.ProjectiveTree
open D5.S3.Quantum.Measurement.Auric.CoordinatePinching
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching (vonNeumannEntropy)

noncomputable section

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

variable {k : ℕ}

def recording (p : CompletePVM ι k) : Matrix (ι × Fin k) ι ℂ :=
  fun x i => p.proj x.2 x.1 i

private theorem pvm_products (p : CompletePVM ι k) (j l : Fin k) :
    p.proj j * p.proj l = if j = l then p.proj j else 0 := by
  by_cases h : j = l
  · subst l
    simp [p.idempotent]
  · simp [h, p.orthogonal j l h]

theorem recording_laws (p : CompletePVM ι k) :
    (recording p)ᴴ * recording p = 1 ∧
      ∀ (ρ : Matrix ι ι ℂ) (j l : Fin k) (a b : ι),
        (recording p * ρ * (recording p)ᴴ) (a, j) (b, l) =
          (p.proj j * ρ * p.proj l) a b := by
  exact recording_isometry_and_state_blocks p.proj
    (fun j => (p.hermitian j).eq) (pvm_products p) p.complete

def recordedState (p : CompletePVM ι k) (ρ : DensityState ι) :
    DensityState (ι × Fin k) := by
  let M := CStarMatrix.ofMatrix.symm ρ.1
  let W := recording p
  refine ⟨CStarMatrix.ofMatrix (W * M * Wᴴ), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    exact ((density_posSemidef ρ).mul_mul_conjTranspose_same W).nonneg
  · change (W * M * Wᴴ).trace = 1
    rw [Matrix.trace_mul_comm (W * M) Wᴴ, ← Matrix.mul_assoc,
      (recording_laws p).1, Matrix.one_mul]
    exact ρ.2.2

def recordLaw (p : CompletePVM ι k) (ρ : DensityState ι) (j : Fin k) : ℝ :=
  (p.proj j * CStarMatrix.ofMatrix.symm ρ.1).trace.re

theorem marginal_system (p : CompletePVM ι k) (ρ : DensityState ι) :
    marginalRight (recordedState p ρ) = (pinchingChannel p).mapState ρ := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  let M := CStarMatrix.ofMatrix.symm ρ.1
  have hchannel :
      CStarMatrix.ofMatrix.symm ((pinchingChannel p).mapState ρ).1 =
        D5.S3.Observer.Conditioning.unreadState p.proj M := by
    change CStarMatrix.ofMatrix.symm ((pinchingChannel p).toCompletelyPositiveMap ρ.1) = _
    exact pinchingChannel_apply p M
  rw [hchannel]
  exact nonselective_recording_marginal p.proj
    (fun j => (p.hermitian j).eq) (pvm_products p) p.complete M

theorem marginal_record (p : CompletePVM ι k) (ρ : DensityState ι) :
    CStarMatrix.ofMatrix.symm (marginalLeft (recordedState p ρ)).1 =
      Matrix.diagonal (fun j => (recordLaw p ρ j : ℂ)) := by
  let M := CStarMatrix.ofMatrix.symm ρ.1
  ext j l
  change (∑ a, (recording p * M * (recording p)ᴴ) (a, j) (a, l)) = _
  simp_rw [(recording_laws p).2]
  change (p.proj j * M * p.proj l).trace = _
  by_cases h : j = l
  · subst l
    rw [Matrix.diagonal_apply_eq]
    have htrace : (p.proj j * M * p.proj j).trace = (p.proj j * M).trace := by
      rw [Matrix.trace_mul_comm (p.proj j * M) (p.proj j), ← Matrix.mul_assoc,
        p.idempotent]
    have hHerm : (p.proj j * M * p.proj j).IsHermitian := by
      simpa only [(p.hermitian j).eq] using
        ((density_posSemidef ρ).mul_mul_conjTranspose_same (p.proj j)).isHermitian
    have hreal : ((p.proj j * M * p.proj j).trace.re : ℂ) =
        (p.proj j * M * p.proj j).trace := by
      simp only [Matrix.trace, Complex.re_sum, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun a _ => congrFun hHerm.coe_re_diag a
    change _ = ((p.proj j * M).trace.re : ℂ)
    rw [← htrace]
    exact hreal.symm
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.trace_mul_comm (p.proj j * M) (p.proj l),
      ← Matrix.mul_assoc, p.orthogonal l j (fun hlj => h hlj.symm), Matrix.zero_mul, Matrix.trace_zero]

theorem recorded_entropy (p : CompletePVM ι k) (ρ : DensityState ι) :
    vonNeumannEntropy (recordedState p ρ) = vonNeumannEntropy ρ := by
  let W := recording p
  let M := CStarMatrix.ofMatrix.symm ρ.1
  have hback : Wᴴ * (W * M) = M := by
    rw [← Matrix.mul_assoc, (recording_laws p).1, Matrix.one_mul]
  rw [entropy_eq_spectral, entropy_eq_spectral]
  unfold spectralEntropy
  have hforward : (W * M * Wᴴ).IsHermitian :=
    (density_posSemidef (recordedState p ρ)).isHermitian
  have hHerm : (Wᴴ * (W * M)).IsHermitian :=
    hback.symm ▸ (density_posSemidef ρ).isHermitian
  have h := spectralSum_mul_reverse Real.negMulLog Real.negMulLog_zero
    (W * M) Wᴴ hforward hHerm
  have hcongr {X Y : Matrix ι ι ℂ} (hxy : X = Y)
      (hX : X.IsHermitian) (hY : Y.IsHermitian) :
      (∑ i, Real.negMulLog (hX.eigenvalues i)) =
        ∑ i, Real.negMulLog (hY.eigenvalues i) := by
    subst Y
    rfl
  exact h.trans (hcongr hback hHerm (density_posSemidef ρ).isHermitian)

theorem marginal_record_entropy (p : CompletePVM ι k) (ρ : DensityState ι) :
    vonNeumannEntropy (marginalLeft (recordedState p ρ)) =
      ∑ j, Real.negMulLog (recordLaw p ρ j) := by
  rw [entropy_eq_spectral]
  exact spectral_sum_eq_of_charpoly_prod (density_posSemidef
    (marginalLeft (recordedState p ρ))).isHermitian (recordLaw p ρ) Real.negMulLog
    (by rw [marginal_record p ρ, Matrix.charpoly_diagonal]; rfl)

theorem projective_record_information (p : CompletePVM ι k) (ρ : DensityState ι) :
    quantumMutualInformation (recordedState p ρ) =
        (vonNeumannEntropy ((pinchingChannel p).mapState ρ) - vonNeumannEntropy ρ) +
          (∑ j, Real.negMulLog (recordLaw p ρ j)) ∧
    vonNeumannEntropy (recordedState p ρ) -
        vonNeumannEntropy (marginalRight (recordedState p ρ)) =
      -(vonNeumannEntropy ((pinchingChannel p).mapState ρ) - vonNeumannEntropy ρ) := by
  unfold quantumMutualInformation
  rw [marginal_system, marginal_record_entropy, recorded_entropy]
  constructor <;> ring

/-- The same coherent recording isometry gives both reduced states and their information
identities. The gain is the entropy of the pinched system minus the entropy of the input. -/
theorem coherent_projective_record (p : CompletePVM ι k) (ρ : DensityState ι) :
    let W := recording p
    let ω := recordedState p ρ
    let M := CStarMatrix.ofMatrix.symm ρ.1
    let gain := vonNeumannEntropy ((pinchingChannel p).mapState ρ) - vonNeumannEntropy ρ
    Wᴴ * W = 1 ∧
    CStarMatrix.ofMatrix.symm ω.1 = W * M * Wᴴ ∧
    marginalRight ω = (pinchingChannel p).mapState ρ ∧
    CStarMatrix.ofMatrix.symm (marginalLeft ω).1 =
      Matrix.diagonal (fun j => (recordLaw p ρ j : ℂ)) ∧
    vonNeumannEntropy ω - vonNeumannEntropy (marginalRight ω) = -gain ∧
    quantumMutualInformation ω = (∑ j, Real.negMulLog (recordLaw p ρ j)) + gain := by
  obtain ⟨hI, hcond⟩ := projective_record_information p ρ
  exact ⟨(recording_laws p).1, rfl, marginal_system p ρ, marginal_record p ρ,
    hcond, hI.trans (add_comm _ _)⟩

end

end D5.S3.Quantum.Measurement.Auric
