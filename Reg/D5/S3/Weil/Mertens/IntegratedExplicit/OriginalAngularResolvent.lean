import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.OriginalAngularResolvent
import Reg.Support.DependentFamily

/-! Exact source-telescope audit attempts. Each term requires the complete
source-family bridge, actual law, variation, sensitivity and observational
dependence as typed input. These inputs and the source selectors have no
inhabitants supplied here. No unconditional four-slot registration is declared. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape

#check fun (arena : DependentFamily.Arena)
    (family : DependentFamily.Registration arena (type_of% @OriginalAngularResolvent.angular_resolvent))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalAngularResolvent.angular_resolvent)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalAngularResolvent.angular_resolvent.__information_unit
    realizationName := Lean.Name.anonymous
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨family⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (DependentFamily.realize arena.signature
      family.actual.readout family.actual.anchor)
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := some selection
    continuation := .unknown
    familyRecord := none
    options := #[] })

#check fun (arena : DependentFamily.Arena)
    (family : DependentFamily.Registration arena (type_of% @OriginalAngularResolvent.cosine_resolvent))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalAngularResolvent.cosine_resolvent)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalAngularResolvent.cosine_resolvent.__information_unit
    realizationName := Lean.Name.anonymous
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨family⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (DependentFamily.realize arena.signature
      family.actual.readout family.actual.anchor)
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := some selection
    continuation := .unknown
    familyRecord := none
    options := #[] })
