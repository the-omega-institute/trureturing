import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzSchwarzRecovery
import Reg.Support.SingleDependentReadout

/-! Owning-mirror registration attempt. It observes each actual conclusion with the
complete original source telescope. No binding certificate is claimed.
Existing certificate boundaries are tracked in https://github.com/the-omega-institute/trureturing/issues/22313.
Source selection is left absent pending the actual compiled source-binding report. -/

noncomputable section
universe u v
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI
open _root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Recovery.PetzSchwarzRecovery
open _root_.D5.S3.Quantum.Recovery.PetzSchwarzRecovery

private def oneState (a : Type u) [Fintype a] [DecidableEq a] [Unique a] : DensityState a :=
  ⟨1, zero_le_one, by simp [Matrix.trace, Matrix.diag, CStarMatrix.one_apply_eq]⟩

private def oneChannel (a : Type u) (b : Type v)
    [Fintype a] [DecidableEq a] [Unique a]
    [Fintype b] [DecidableEq b] [Unique b] : QuantumChannel a b where
  toCompletelyPositiveMap := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (CStarMatrix.reindexₐ ℂ ℂ (Equiv.ofUnique a b))
  trace_preserving := by
    intro X
    change Matrix.trace (CStarMatrix.reindexₐ ℂ ℂ (Equiv.ofUnique a b) X) = Matrix.trace X
    simp [Matrix.trace, Matrix.diag, CStarMatrix.reindexₐ_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    change X ((Equiv.ofUnique a b).symm default) ((Equiv.ofUnique a b).symm default) =
      X default default
    simp only [Subsingleton.elim ((Equiv.ofUnique a b).symm default) (default : a)]

/-- The readout retains all three conjuncts, including the supported Gram bound. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Prop) (fun _ => Prop → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ∧ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ),
    let H := cfc Real.sqrt M.data.S
    let W := spectralInverseSqrt M.data.Q
    let Y := W * cfc Real.sqrt M.data.T
    let A := H * M.data.Ψ Y
    let C := A * spectralSupport M.data.R
    let N := H * M.data.Ψ (W * M.data.T * W) * H
    R.readout () () (A * Aᴴ ≤ N) (C * Cᴴ ≤ N ∧ N.trace = M.data.R.trace)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  let a := ULift.{u} Unit
  let b := ULift.{v} Unit
  let ρ := oneState a
  let Φ := oneChannel a b
  let M := supported_relative_modular_model Φ ρ ρ (supportContained_refl ρ)
  exact @h a b inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance Φ ρ ρ M

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have h := congrFun he True
  simp [actual, realize] at h

def family : Registration arena.{u,v} (type_of% @petz_core_schwarz_and_trace.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@petz_core_schwarz_and_trace.{u,v}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@petz_core_schwarz_and_trace.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzSchwarzRecovery.petz_core_schwarz_and_trace.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzSchwarzRecovery.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ∧ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Recovery.PetzSchwarzRecovery
