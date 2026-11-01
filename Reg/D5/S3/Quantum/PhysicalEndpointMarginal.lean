import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.PhysicalEndpointMarginal
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.PhysicalEndpointMarginal

open _root_.D5.S3.Quantum.PhysicalEndpointMarginal
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

structure Case where
  Sector : Type u
  fintype : Fintype Sector
  decEq : DecidableEq Sector
  d : Sector → ℕ
  hd : ∀ s, 0 < d s
  Y : Matrix Sector Sector ℂ

def actualReadout (p : Case.{u}) : Prop :=
  letI := p.fintype
  letI := p.decEq
  partialTraceRight (encodedTarget p.d p.Y) = targetMarginal p.d p.Y ∧
    partialTraceLeft (encodedTarget p.d p.Y) = targetMarginal p.d p.Y

abbrev signature : Signature where
  Params := Case.{u}
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ s => s = true) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ p : Case.{u}, R.readout () p true ↔ actualReadout p

theorem actual_law : arena.{u}.Law actual.{u} := by
  intro p
  constructor
  · intro _
    letI := p.fintype
    letI := p.decEq
    simpa [actualReadout] using (result p.d p.hd p.Y)
  · intro _
    simp [actual, realize]

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let p : Case.{u} := {
    Sector := ULift.{u} Unit
    fintype := inferInstance
    decEq := inferInstance
    d := fun _ => 1
    hd := by intro; decide
    Y := 0 }
  have hp := h p
  have hgood : actualReadout p := by
    dsimp [actualReadout, p]
    exact result (fun _ : ULift.{u} Unit => 1) (by intro; decide) 0
  have hbad := hp.mpr hgood
  simp [rejected, realize] at hbad

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Quantum.PhysicalEndpointMarginal.result.{u})) ↔
      arena.{u}.Law actual.{u} := by
  constructor
  · intro h p
    constructor
    · intro _
      letI := p.fintype
      letI := p.decEq
      simpa [actualReadout] using (h p.d p.hd p.Y)
    · intro _
      simp [actual, realize]
  · intro h Sector _ _ d hd Y
    let p : Case.{u} := {
      Sector := Sector
      fintype := inferInstance
      decEq := inferInstance
      d := d
      hd := hd
      Y := Y }
    have hp := h p
    have hgood : actualReadout p := hp.mp (by simp [actual, realize])
    letI := p.fintype
    letI := p.decEq
    simpa [actualReadout] using hgood

private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro _
  let p : Case.{u} := {
    Sector := ULift.{u} Unit
    fintype := inferInstance
    decEq := inferInstance
    d := fun _ => 1
    hd := by intro; decide
    Y := 0 }
  refine ⟨p, false, true, ?_⟩
  change (false = true) ≠ (true = true)
  simp

def registration :
    Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.PhysicalEndpointMarginal.result.{u})) where
  actual := actual.{u}
  bridge := source_bridge.{u}
  variation := ⟨source_bridge.{u}.mp result, rejected.{u}, rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u}, ?_, rfl, rejected_law.{u}⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence.{u}

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.PhysicalEndpointMarginal.result.{u})
    (type_of% actual.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.PhysicalEndpointMarginal.result.__information_unit
  realizationName := `Reg.D5.S3.Quantum.PhysicalEndpointMarginal.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual.{u}
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms actual_law
#print axioms rejected_law
#print axioms source_bridge
#print axioms dependence
#print axioms registration
#print axioms audit

end Reg.D5.S3.Quantum.PhysicalEndpointMarginal
