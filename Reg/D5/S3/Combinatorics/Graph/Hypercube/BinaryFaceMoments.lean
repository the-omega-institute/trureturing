/- GID: Reg/D5/S3/Combinatorics/Graph/Hypercube/BinaryFaceMoments
   generality: G
   mirror-B: none
   mirror-E: none
   anchors: []
   utility: none
   digest: Source-bound audits of adjacency and the all-orders face moment readout. -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Hypercube.BinaryFaceMoments
import Reg.Support.SingleDependentReadout

/-! Dependent readouts for the binary face-moment operator and characterization. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryFaceMoments

open _root_.D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment
open _root_.D5.S3.Combinatorics.Graph.Hypercube.BinaryFaceMoments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Word (n : ℕ) := Finset (Fin n) → ZMod 2

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ Word Word

def adjacencyReadout : Realization signature :=
  realize signature (fun _ _ f => adjacency f) (fun e => nomatch e)

def momentReadout : Realization signature :=
  realize signature (fun _ _ f => faceMoment f) (fun e => nomatch e)

def constantOne : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

abbrev operatorArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (f : Word n) (S : Finset (Fin n)),
    faceMoment (R.readout () n f) S =
      (n : ZMod 2) * faceMoment f S + ∑ i ∈ S, faceMoment f (S.erase i)

private theorem constantOne_fails_operator : ¬ operatorArena.Law constantOne := by
  intro h
  have hne : faceMoment (n := 0) (fun _ => 1) ∅ ≠
      (0 : ZMod 2) * faceMoment (0 : Word 0) ∅ +
        ∑ i ∈ (∅ : Finset (Fin 0)), faceMoment (0 : Word 0) (Finset.erase ∅ i) := by decide
  exact hne (@h 0 0 ∅)

private theorem adjacency_depends_on_word : ObservationalDependence signature adjacencyReadout := by
  intro role
  refine ⟨1, 0, (fun _ => 1), ?_⟩
  intro h
  have hne : adjacency (0 : Word 1) ∅ ≠ adjacency (n := 1) (fun _ => 1) ∅ := by decide
  exact hne (congrFun h ∅)

def operatorFamily : Registration operatorArena (type_of% (@faceMoment_adjacency)) where
  actual := adjacencyReadout
  bridge := Iff.rfl
  variation := ⟨@faceMoment_adjacency, constantOne, constantOne_fails_operator⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    operatorArena.Law adjacencyReadout constantOne constantOne_fails_operator
  dependence := adjacency_depends_on_word

abbrev characterizationArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (f : Word n), adjacency f = (n : ZMod 2) • f ↔
    ∀ S : Finset (Fin n), (∑ i ∈ S, R.readout () n f (S.erase i)) = 0

private theorem constantOne_fails_characterization : ¬ characterizationArena.Law constantOne := by
  intro h
  have hz : adjacency (0 : Word 1) = (1 : ZMod 2) • (0 : Word 1) := by
    funext x
    simp [adjacency]
  have hsum := ((@h 1 0).mp hz) {(0 : Fin 1)}
  change (∑ _ ∈ ({0} : Finset (Fin 1)), (1 : ZMod 2)) = 0 at hsum
  simp at hsum

private theorem moment_depends_on_word : ObservationalDependence signature momentReadout := by
  intro role
  refine ⟨0, 0, (fun _ => 1), ?_⟩
  intro h
  have hne : faceMoment (0 : Word 0) ∅ ≠ faceMoment (n := 0) (fun _ => 1) ∅ := by decide
  exact hne (congrFun h ∅)

def characterizationFamily :
    Registration characterizationArena (type_of% (@adjacency_eq_dim_smul_iff)) where
  actual := momentReadout
  bridge := Iff.rfl
  variation := ⟨@adjacency_eq_dim_smul_iff, constantOne, constantOne_fails_characterization⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    characterizationArena.Law momentReadout constantOne constantOne_fails_characterization
  dependence := moment_depends_on_word

def operatorAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@faceMoment_adjacency) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.Hypercube.BinaryFaceMoments.faceMoment_adjacency.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryFaceMoments.operatorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨operatorArena⟩
  objectArena := .source ⟨operatorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source operatorArena ⟨operatorFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => adjacency f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Hypercube.BinaryFaceMoments
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def characterizationAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@adjacency_eq_dim_smul_iff) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Graph.Hypercube.BinaryFaceMoments.adjacency_eq_dim_smul_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryFaceMoments.characterizationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨characterizationArena⟩
  objectArena := .source ⟨characterizationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source characterizationArena ⟨characterizationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => faceMoment f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Hypercube.BinaryFaceMoments
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "fn", "arg", "arg", "body", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryFaceMoments
