import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzCoreTraceStability
import Reg.Support.SingleDependentReadout

/-! Owning-mirror registration attempt. It observes each actual conclusion with the
complete original source telescope. No binding certificate is claimed.
Existing certificate boundaries are tracked in https://github.com/the-omega-institute/trureturing/issues/22313.
Source selection is left absent pending the actual compiled source-binding report. -/

noncomputable section
universe u v
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI
open _root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Recovery.PetzCoreTraceStability
open _root_.D5.S3.Quantum.Recovery.PetzCoreTraceStability
open _root_.D5.S3.Quantum.Recovery.PetzPhysicalWeightedCoordinates

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

namespace PhysicalTraceBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ),
    R.readout () ()
      (traceNorm (cfc Real.sqrt M.data.S * M.data.Ψ
        (spectralInverseSqrt M.data.Q * M.data.T * spectralInverseSqrt M.data.Q) *
        cfc Real.sqrt M.data.S - M.data.R))
      (4 * ‖physicalWeightedError M
        (cfc (fun t : ℝ => 1 / Real.sqrt t) M.data.B *ᵥ M.data.η)‖)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  let a := ULift.{u} Unit
  let b := ULift.{v} Unit
  let ρ := oneState a
  let Φ := oneChannel a b
  let M := supported_relative_modular_model Φ ρ ρ (supportContained_refl ρ)
  exact @h a b inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance Φ ρ ρ M

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena.{u,v} (type_of% @petz_core_traceNorm_le_four_physical_hs.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@petz_core_traceNorm_le_four_physical_hs.{u,v}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@petz_core_traceNorm_le_four_physical_hs.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzCoreTraceStability.petz_core_traceNorm_le_four_physical_hs.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzCoreTraceStability.PhysicalTraceBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
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

end PhysicalTraceBound

namespace WeightedTraceBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ)
    (L : ℝ) (_hL0 : 0 ≤ L)
    (_hL : ∀ ji : M.data.J × M.data.I, M.data.sj ji.1 / M.data.ri ji.2 ≤ L),
    let x := cfc (fun t : ℝ => 1 / Real.sqrt t) M.data.B *ᵥ M.data.η
    let d := modularCoordinateError M x
    R.readout () ()
      (traceNorm (cfc Real.sqrt M.data.S * M.data.Ψ
        (spectralInverseSqrt M.data.Q * M.data.T * spectralInverseSqrt M.data.Q) *
        cfc Real.sqrt M.data.S - M.data.R))
      (4 * Real.sqrt L * Real.sqrt (star d ⬝ᵥ d).re)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  let a := ULift.{u} Unit
  let b := ULift.{v} Unit
  let ρ := oneState a
  let Φ := oneChannel a b
  let M := supported_relative_modular_model Φ ρ ρ (supportContained_refl ρ)
  let L := ∑ ji : M.data.J × M.data.I, |M.data.sj ji.1 / M.data.ri ji.2|
  have hL (ji : M.data.J × M.data.I) : M.data.sj ji.1 / M.data.ri ji.2 ≤ L := by
    exact (le_abs_self _).trans (Finset.single_le_sum
      (fun k _ => abs_nonneg (M.data.sj k.1 / M.data.ri k.2)) (Finset.mem_univ ji))
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun ji _ => abs_nonneg _)
  exact @h a b inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance Φ ρ ρ M L hL0 hL

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena.{u,v} (type_of% @petz_core_traceNorm_le_weighted_inverse_sqrt_error.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@petz_core_traceNorm_le_weighted_inverse_sqrt_error.{u,v}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@petz_core_traceNorm_le_weighted_inverse_sqrt_error.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzCoreTraceStability.petz_core_traceNorm_le_weighted_inverse_sqrt_error.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzCoreTraceStability.WeightedTraceBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
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

end WeightedTraceBound

end Reg.D5.S3.Quantum.Recovery.PetzCoreTraceStability
