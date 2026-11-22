import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzRetainedQubitPairing
import Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
import Reg.Support.SingleDependentReadout

/-! Source-bound readouts of the ordinary Petz squared trace error bounds. -/

set_option autoImplicit false

noncomputable section

universe u

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI
open _root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralInverseSqrt spectralSupport)
open _root_.D5.S3.Quantum.Recovery.PetzRetainedQubitPairing
open scoped BigOperators ComplexOrder MatrixOrder

open private unitState unitChannel from Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip

namespace Reg.D5.S3.Quantum.Recovery.PetzRetainedQubitPairing

private abbrev scalarSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence scalarSignature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [actual, realize] at he

namespace AllGaps

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {a b : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Φ : QuantumChannel a b) (σ : DensityState a),
    let K := (actual_kraus_representation Φ).kraus
    let S := CStarMatrix.ofMatrix.symm σ.1
    let Q := CStarMatrix.ofMatrix.symm (Φ.mapState σ).1
    let H := cfc Real.sqrt S
    let W := spectralInverseSqrt Q
    let P := spectralSupport Q
    ∃ recovery : QuantumChannel b a,
      (∀ X : Matrix b b ℂ,
        CStarMatrix.ofMatrix.symm
          (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          (∑ c, H * (K c)ᴴ * W * X * W * K c * H) +
            Matrix.trace ((1 - P) * X) • S) ∧
      recovery.mapState (Φ.mapState σ) = σ ∧
      ∀ (ρ : DensityState a) (support : SupportContained ρ σ),
        let M := supported_relative_modular_model Φ ρ σ support
        let error := traceNorm (CStarMatrix.ofMatrix.symm ρ.1 -
          CStarMatrix.ofMatrix.symm (recovery.mapState (Φ.mapState ρ)).1) ^ 2
        let Δ := finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)
        M.data.Q.rank ≤ 2 → R.readout () () error ((8 + 2 * Real.sqrt 2) * Δ)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let n := ULift.{u} Unit
  let σ : DensityState n := unitState n
  let Φ : QuantumChannel n n := unitChannel n n
  obtain ⟨_, _, _, hb⟩ := h Φ σ
  let M := supported_relative_modular_model Φ σ σ (supportContained_refl σ)
  have hQ : M.data.Q.rank ≤ 2 := M.data.Q.rank_le_card_width.trans (by simp [n])
  exact hb σ (supportContained_refl σ) hQ

def family : Registration arena.{u} (type_of% @ordinary_petz_traceNorm_sq_le_of_qubit_output.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ordinary_petz_traceNorm_sq_le_of_qubit_output.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ordinary_petz_traceNorm_sq_le_of_qubit_output.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzRetainedQubitPairing.ordinary_petz_traceNorm_sq_le_of_qubit_output.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzRetainedQubitPairing.AllGaps.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzRetainedQubitPairing
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #[
          "body", "body", "body", "body", "body", "body", "body", "body",
          "body", "body", "body", "body", "body", "body", "body", "body",
          "arg", "body", "arg", "arg", "body", "body", "body", "body", "body", "body",
          "fn", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AllGaps

namespace Separated

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {a b : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Φ : QuantumChannel a b) (σ : DensityState a),
    let K := (actual_kraus_representation Φ).kraus
    let S := CStarMatrix.ofMatrix.symm σ.1
    let Q := CStarMatrix.ofMatrix.symm (Φ.mapState σ).1
    let H := cfc Real.sqrt S
    let W := spectralInverseSqrt Q
    let P := spectralSupport Q
    ∃ recovery : QuantumChannel b a,
      (∀ X : Matrix b b ℂ,
        CStarMatrix.ofMatrix.symm
          (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          (∑ c, H * (K c)ᴴ * W * X * W * K c * H) +
            Matrix.trace ((1 - P) * X) • S) ∧
      recovery.mapState (Φ.mapState σ) = σ ∧
      ∀ (ρ : DensityState a) (support : SupportContained ρ σ),
        let M := supported_relative_modular_model Φ ρ σ support
        let error := traceNorm (CStarMatrix.ofMatrix.symm ρ.1 -
          CStarMatrix.ofMatrix.symm (recovery.mapState (Φ.mapState ρ)).1) ^ 2
        let Δ := finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)
        M.data.Q.rank ≤ 2 →
          (M.data.T.rank ≤ 1 → R.readout () () error (8 * Δ)) ∧
          (M.data.T.rank = 2 →
            (∀ j k : M.data.K, j ≠ k →
              logisticCorrelation (Real.log (M.data.pk j) - Real.log (M.data.pk k)) ≤ 1 / 5) →
            (∀ i l : M.data.L, i ≠ l →
              logisticCorrelation (Real.log (M.data.ql i) - Real.log (M.data.ql l)) ≤ 1 / 5) →
            error ≤ (8 + 2 * Real.sqrt 2) * Δ)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let n := ULift.{u} Unit
  let σ : DensityState n := unitState n
  let Φ : QuantumChannel n n := unitChannel n n
  obtain ⟨_, _, _, hb⟩ := h Φ σ
  let M := supported_relative_modular_model Φ σ σ (supportContained_refl σ)
  have hQ : M.data.Q.rank ≤ 2 := M.data.Q.rank_le_card_width.trans (by simp [n])
  have hT : M.data.T.rank ≤ 1 := M.data.T.rank_le_card_width.trans (by simp [n])
  exact (hb σ (supportContained_refl σ) hQ).1 hT

def family : Registration arena.{u} (type_of% @ordinary_petz_traceNorm_sq_le_of_qubit_gaps.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ordinary_petz_traceNorm_sq_le_of_qubit_gaps.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ordinary_petz_traceNorm_sq_le_of_qubit_gaps.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzRetainedQubitPairing.ordinary_petz_traceNorm_sq_le_of_qubit_gaps.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzRetainedQubitPairing.Separated.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzRetainedQubitPairing
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #[
          "body", "body", "body", "body", "body", "body", "body", "body",
          "body", "body", "body", "body", "body", "body", "body", "body",
          "arg", "body", "arg", "arg", "body", "body", "body", "body", "body", "body",
          "fn", "arg", "body", "fn", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Separated

end Reg.D5.S3.Quantum.Recovery.PetzRetainedQubitPairing
