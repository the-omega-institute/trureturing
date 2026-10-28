import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Lattices.Golay.GolayOctadIncidence
import Reg.Support.SingleDependentReadout

noncomputable section
namespace Reg.D5.S3.Arith.Lattices.Golay.GolayOctadIncidence
open _root_.D5.S3.Arith.Lattices.Golay.GolayEncoder
open _root_.D5.S3.Arith.Lattices.Golay.GolayOctadCount
open _root_.D5.S3.Arith.Lattices.Golay.LeechSignedSupport
open _root_.D5.S3.Arith.Lattices.Golay.GolayOctadIncidence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
attribute [local instance] Classical.propDecidable
attribute [local instance 10] Fintype.ofFinite

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Word) (fun _ => Finset (Fin 24))

def actual : Realization signature :=
  realize signature (fun _ _ w => wordSupport w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro r
  refine ⟨(), 0, (fun _ => 1), ?_⟩
  change wordSupport (0 : Word) ≠ wordSupport (fun _ => 1)
  intro h
  have hc := congrArg (fun s : Finset (Fin 24) => (0 : Fin 24) ∈ s) h
  simpa [wordSupport] using hc

abbrev steinerArena : Arena where
  signature := signature
  Law R := ∀ (T : Finset (Fin 24)), T.card = 5 →
    ∃! c : Octad, T ⊆ R.readout () () (c.val : Word)

private theorem rejected_steiner : ¬ steinerArena.Law rejected := by
  intro h
  let T : Finset (Fin 24) := {0, 1, 2, 3, 4}
  obtain ⟨c, hc, _⟩ := h T (by decide +kernel)
  have h0 := hc (show (0 : Fin 24) ∈ T by decide +kernel)
  simpa [rejected, realize] using h0

def steinerEvidence : Registration steinerArena (type_of% (@steiner_five)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨steiner_five, rejected, rejected_steiner⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_steiner
  dependence := actual_dependence

abbrev incidenceArena : Arena where
  signature := signature
  Law R := ∀ (i j : Fin 24), i ≠ j →
    (Finset.univ.filter fun c : Octad => i ∈ R.readout () () (c.val : Word)).card = 253 ∧
    (Finset.univ.filter fun c : Octad => j ∈ R.readout () () (c.val : Word)).card = 253 ∧
    (Finset.univ.filter fun c : Octad =>
      i ∈ R.readout () () (c.val : Word) ∧ j ∈ R.readout () () (c.val : Word)).card = 77 ∧
    (Finset.univ.filter fun c : Octad =>
      (i ∈ R.readout () () (c.val : Word) ∧ j ∉ R.readout () () (c.val : Word)) ∨
      (i ∉ R.readout () () (c.val : Word) ∧ j ∈ R.readout () () (c.val : Word))).card = 352 ∧
    (Finset.univ.filter fun c : Octad =>
      i ∉ R.readout () () (c.val : Word) ∧ j ∉ R.readout () () (c.val : Word)).card = 330

private theorem rejected_incidence : ¬ incidenceArena.Law rejected := by
  intro h
  have hc := (h 0 1 (by decide +kernel)).1
  simpa [rejected, realize] using hc

def incidenceEvidence : Registration incidenceArena (type_of% (@coordinate_incidence)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨coordinate_incidence, rejected, rejected_incidence⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_incidence
  dependence := actual_dependence

def steinerRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@steiner_five)
    (type_of% (realize signature (fun _ _ w => wordSupport w) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Arith.Lattices.Golay.GolayOctadIncidence.steiner_five.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.Golay.GolayOctadIncidence.steinerEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨steinerArena⟩
  objectArena := .source ⟨steinerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source steinerArena ⟨steinerEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => wordSupport w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Word
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def incidenceRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coordinate_incidence)
    (type_of% (realize signature (fun _ _ w => wordSupport w) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Arith.Lattices.Golay.GolayOctadIncidence.coordinate_incidence.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.Golay.GolayOctadIncidence.incidenceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨incidenceArena⟩
  objectArena := .source ⟨incidenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source incidenceArena ⟨incidenceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => wordSupport w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Word
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms steinerEvidence
#print axioms incidenceEvidence

end Reg.D5.S3.Arith.Lattices.Golay.GolayOctadIncidence
