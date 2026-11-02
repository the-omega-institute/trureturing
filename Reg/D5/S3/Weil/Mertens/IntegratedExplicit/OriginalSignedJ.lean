import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.OriginalSignedJ
import Reg.Support.DependentFamily

/-! Exact source-telescope audit attempts. Each term requires the complete
source-family bridge, actual law, variation, sensitivity and observational
dependence as typed input. These inputs and the source selectors have no
inhabitants supplied here. No unconditional four-slot registration is declared. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape

#check fun (arena : DependentFamily.Arena)
    (family : DependentFamily.Registration arena (type_of% @OriginalSignedJ.indicator_tail_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalSignedJ.indicator_tail_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalSignedJ.indicator_tail_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalSignedJ.integral_indicator_tail))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalSignedJ.integral_indicator_tail)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalSignedJ.integral_indicator_tail.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalSignedJ.finiteB_mul_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalSignedJ.finiteB_mul_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalSignedJ.finiteB_mul_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalSignedJ.finite_abel_ac))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalSignedJ.finite_abel_ac)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalSignedJ.finite_abel_ac.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalSignedJ.cutoff_knot))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalSignedJ.cutoff_knot)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalSignedJ.cutoff_knot.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalSignedJ.finiteB_eq_b))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalSignedJ.finiteB_eq_b)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalSignedJ.finiteB_eq_b.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalSignedJ.testLift_ac))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalSignedJ.testLift_ac)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalSignedJ.testLift_ac.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalSignedJ.testLift_ae_deriv))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalSignedJ.testLift_ae_deriv)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalSignedJ.testLift_ae_deriv.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalSignedJ.original_integrands_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalSignedJ.original_integrands_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalSignedJ.original_integrands_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalSignedJ.weight_testLift))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalSignedJ.weight_testLift)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalSignedJ.weight_testLift.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalSignedJ.original_J_identity))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalSignedJ.original_J_identity)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalSignedJ.original_J_identity.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalSignedJ.fullR_eq_original_J))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalSignedJ.fullR_eq_original_J)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalSignedJ.fullR_eq_original_J.__information_unit
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
