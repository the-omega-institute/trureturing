import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzPhysicalWeightedCoordinates
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

namespace Reg.D5.S3.Quantum.Recovery.PetzPhysicalWeightedCoordinates
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

private theorem positive_pair
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ) : Nonempty (M.data.J × M.data.I) := by
  classical
  by_contra h
  letI : IsEmpty (M.data.J × M.data.I) := ⟨fun ji => h ⟨ji⟩⟩
  have hn := M.normξ
  simp at hn

namespace PositiveCoordinate

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ)
    (x : M.data.L × M.data.K → ℂ) (j : M.data.J) (i : M.data.I),
    R.readout () () (star (M.data.v j) ⬝ᵥ (physicalWeightedError M x *ᵥ M.data.u i))
      (-(Real.sqrt (M.data.sj j / M.data.ri i) : ℂ) * modularCoordinateError M x (j, i))

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  let a := ULift.{u} Unit
  let b := ULift.{v} Unit
  let ρ := oneState a
  let Φ := oneChannel a b
  let M := supported_relative_modular_model Φ ρ ρ (supportContained_refl ρ)
  let ji := Classical.choice (positive_pair M)
  exact @h a b inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance Φ ρ ρ M 0 ji.1 ji.2

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena.{u,v} (type_of% @physical_positive_coordinate.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@physical_positive_coordinate.{u,v}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_positive_coordinate.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzPhysicalWeightedCoordinates.physical_positive_coordinate.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzPhysicalWeightedCoordinates.PositiveCoordinate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
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

end PositiveCoordinate

namespace WeightedParseval

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ)
    (x : M.data.L × M.data.K → ℂ),
    R.readout () () (‖physicalWeightedError M x‖ ^ 2)
      (∑ ji : M.data.J × M.data.I,
        (M.data.sj ji.1 / M.data.ri ji.2) * ‖modularCoordinateError M x ji‖ ^ 2)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  let a := ULift.{u} Unit
  let b := ULift.{v} Unit
  let ρ := oneState a
  let Φ := oneChannel a b
  let M := supported_relative_modular_model Φ ρ ρ (supportContained_refl ρ)
  exact @h a b inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance Φ ρ ρ M 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena.{u,v} (type_of% @physical_weighted_parseval.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@physical_weighted_parseval.{u,v}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_weighted_parseval.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzPhysicalWeightedCoordinates.physical_weighted_parseval.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzPhysicalWeightedCoordinates.WeightedParseval.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
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

end WeightedParseval

namespace PhysicalUpperBound

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
    (x : M.data.L × M.data.K → ℂ) (L : ℝ)
    (_hL : ∀ ji : M.data.J × M.data.I, M.data.sj ji.1 / M.data.ri ji.2 ≤ L),
    R.readout () () (‖physicalWeightedError M x‖ ^ 2)
      (L * ∑ ji, ‖modularCoordinateError M x ji‖ ^ 2)

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
  exact @h a b inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance Φ ρ ρ M 0 L hL

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena.{u,v} (type_of% @physical_hs_sq_le_coordinate_sq.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@physical_hs_sq_le_coordinate_sq.{u,v}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_hs_sq_le_coordinate_sq.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzPhysicalWeightedCoordinates.physical_hs_sq_le_coordinate_sq.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzPhysicalWeightedCoordinates.PhysicalUpperBound.family
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

end PhysicalUpperBound

end Reg.D5.S3.Quantum.Recovery.PetzPhysicalWeightedCoordinates
