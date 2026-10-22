import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.BcGhostLZeroSpectrum
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.BcGhostFockSupport
open _root_.D5.S3.VertexAlgebra.BcGhostLZeroSpectrum

namespace Reg.D5.S3.VertexAlgebra.BcGhostLZeroSpectrum

universe scalarLevel
noncomputable section

structure Parameters where
  K : Type scalarLevel
  ring : CommRing K

abbrev signature : Signature where
  Params := Parameters.{scalarLevel}
  State parameter := Finset ℕ × parameter.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := letI := parameter.ring; Fock parameter.K
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{scalarLevel} :=
  realize signature (fun _ parameter state => letI := parameter.ring
    L 0 (Finsupp.single state.1 state.2)) (fun empty => nomatch empty)

def zeroReplacement : Realization signature.{scalarLevel} :=
  realize signature (fun _ parameter _ => letI := parameter.ring; 0)
    (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature.{scalarLevel}
  Law readout := ∀ {K : Type scalarLevel} [CommRing K] (subset : Finset ℕ) (scalar : K),
    readout.readout () ⟨K, inferInstance⟩ (subset, scalar) =
      (energy subset : K) • Finsupp.single subset scalar

def statement : Prop := ∀ {K : Type scalarLevel} [CommRing K]
    (subset : Finset ℕ) (scalar : K),
  L (K := K) 0 (Finsupp.single subset scalar) =
    (energy subset : K) • Finsupp.single subset scalar

theorem sourceReconstruction :
    statement.{scalarLevel} ↔ arena.{scalarLevel}.Law actual := Iff.rfl

theorem actualPositive : arena.{scalarLevel}.Law actual := by
  intro K ring subset scalar
  simpa only [actual, realize] using L_zero_single (K := K) subset scalar

theorem rejected : ¬ arena.{scalarLevel}.Law zeroReplacement := by
  intro law
  have equation := law (K := ULift.{scalarLevel} ℤ) {1} 1
  have detected := congrArg (fun ghost : Fock (ULift.{scalarLevel} ℤ) => ghost {1}) equation
  norm_num [zeroReplacement, realize, energy, siteWeight] at detected

theorem dependence : ObservationalDependence signature.{scalarLevel} actual := by
  intro role
  refine ⟨⟨ULift.{scalarLevel} ℤ, inferInstance⟩, ({1}, 1), (∅, 1), ?_⟩
  intro equality
  have detected := congrArg (fun ghost : Fock (ULift.{scalarLevel} ℤ) => ghost {1}) equality
  norm_num [actual, realize, L_zero_single, energy, siteWeight] at detected

def source : Registration arena.{scalarLevel} statement.{scalarLevel} where
  actual := actual
  bridge := sourceReconstruction
  variation := ⟨actualPositive, zeroReplacement, rejected⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨zeroReplacement, ?_, rfl, rejected⟩
      intro other distinct
      exact (distinct (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := dependence

def registration : Contract.Registration
    (@_root_.D5.S3.VertexAlgebra.BcGhostLZeroSpectrum.L_zero_single.{scalarLevel})
    (Realization signature.{scalarLevel}) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.BcGhostLZeroSpectrum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostLZeroSpectrum.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms sourceReconstruction
#print axioms actualPositive
#print axioms rejected
#print axioms dependence
#print axioms source
#print axioms registration

end

end Reg.D5.S3.VertexAlgebra.BcGhostLZeroSpectrum
