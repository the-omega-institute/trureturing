import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier
import Reg.Support.DependentFamily

/-! Exact source-telescope audit attempts. Each term requires the complete
source-family bridge, actual law, variation, sensitivity and observational
dependence as typed input. These inputs and the source selectors have no
inhabitants supplied here. No unconditional four-slot registration is declared. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape

#check fun (arena : DependentFamily.Arena)
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.phase_norm))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.phase_norm)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.phase_norm.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.phase_continuous))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.phase_continuous)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.phase_continuous.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.phase_add))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.phase_add)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.phase_add.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.phase_conj))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.phase_conj)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.phase_conj.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.phase_re))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.phase_re)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.phase_re.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.phase_neg_left))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.phase_neg_left)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.phase_neg_left.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.transform_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.transform_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.transform_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.Ahat_bound))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.Ahat_bound)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.Ahat_bound.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.Ahat_continuous))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.Ahat_continuous)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.Ahat_continuous.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.prefix_eq_steps))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.prefix_eq_steps)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.prefix_eq_steps.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.prefix_measurable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.prefix_measurable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.prefix_measurable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.prefix_zero_off_window))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.prefix_zero_off_window)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.prefix_zero_off_window.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.prefix_eq_zero_extension))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.prefix_eq_zero_extension)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.prefix_eq_zero_extension.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.prefix_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.prefix_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.prefix_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.prefix_L1_L2))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.prefix_L1_L2)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.prefix_L1_L2.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.frequency_mul_Ahat))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.frequency_mul_Ahat)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.frequency_mul_Ahat.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.frequency_Ahat_bound))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.frequency_Ahat_bound)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.frequency_Ahat_bound.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.normSq_Ahat_bound))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.normSq_Ahat_bound)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.normSq_Ahat_bound.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.normSq_Ahat_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.normSq_Ahat_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.normSq_Ahat_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.density_nonneg))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.density_nonneg)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.density_nonneg.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.density_continuous))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.density_continuous)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.density_continuous.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualFourier.actual_rho_finite))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualFourier.actual_rho_finite)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier.actual_rho_finite.__information_unit
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
