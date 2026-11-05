import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.OriginalTestRegularity
import Reg.Support.DependentFamily

/-! Exact source-telescope audit attempts. Each term requires the complete
source-family bridge, actual law, variation, sensitivity and observational
dependence as typed input. These inputs and the source selectors have no
inhabitants supplied here. No unconditional four-slot registration is declared. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape

#check fun (arena : DependentFamily.Arena)
    (family : DependentFamily.Registration arena (type_of% @OriginalTestRegularity.ramp_lipschitz))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalTestRegularity.ramp_lipschitz)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalTestRegularity.ramp_lipschitz.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalTestRegularity.finite_sum_ac))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalTestRegularity.finite_sum_ac)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalTestRegularity.finite_sum_ac.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalTestRegularity.c_eq_hinges))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalTestRegularity.c_eq_hinges)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalTestRegularity.c_eq_hinges.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalTestRegularity.c_ac))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalTestRegularity.c_ac)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalTestRegularity.c_ac.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalTestRegularity.c_at_D))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalTestRegularity.c_at_D)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalTestRegularity.c_at_D.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalTestRegularity.denom_pos))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalTestRegularity.denom_pos)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalTestRegularity.denom_pos.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalTestRegularity.spectralKernel_continuous))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalTestRegularity.spectralKernel_continuous)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalTestRegularity.spectralKernel_continuous.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalTestRegularity.spectralKernel_bound))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalTestRegularity.spectralKernel_bound)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalTestRegularity.spectralKernel_bound.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalTestRegularity.spectralKernel_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalTestRegularity.spectralKernel_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalTestRegularity.spectralKernel_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalTestRegularity.spectralS_ac))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalTestRegularity.spectralS_ac)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalTestRegularity.spectralS_ac.__information_unit
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
