import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint
import Reg.Support.DependentFamily

/-! Exact source-telescope audit attempts. Each term requires the complete
source-family bridge, actual law, variation, sensitivity and observational
dependence as typed input. These inputs and the source selectors have no
inhabitants supplied here. No unconditional four-slot registration is declared. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape

#check fun (arena : DependentFamily.Arena)
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.denominator_pos))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.denominator_pos)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.denominator_pos.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.weight_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.weight_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.weight_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.resolvent_norm))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.resolvent_norm)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.resolvent_norm.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.resolvent_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.resolvent_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.resolvent_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.normalized_resolvent))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.normalized_resolvent)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.normalized_resolvent.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.conjugate_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.conjugate_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.conjugate_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.coefficient_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.coefficient_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.coefficient_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.coefficient_norm))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.coefficient_norm)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.coefficient_norm.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.coefficient_re_swap))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.coefficient_re_swap)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.coefficient_re_swap.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.fourierPair_eq_product))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.fourierPair_eq_product)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.fourierPair_eq_product.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.fourierPair_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.fourierPair_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.fourierPair_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.Ahat_normSq_eq_pair))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.Ahat_normSq_eq_pair)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.Ahat_normSq_eq_pair.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.triple_norm))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.triple_norm)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.triple_norm.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.triple_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.triple_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.triple_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.pair_expansion))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.pair_expansion)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.pair_expansion.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.frequencyIntegrand_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.frequencyIntegrand_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.frequencyIntegrand_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.decay_nonneg))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.decay_nonneg)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.decay_nonneg.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.decay_le_one))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.decay_le_one)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.decay_le_one.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.spatial_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.spatial_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.spatial_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.complex_resolvent_identity))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.complex_resolvent_identity)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.complex_resolvent_identity.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.spectralS_density))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.spectralS_density)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.spectralS_density.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.spectralS_eq_complex_real))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.spectralS_eq_complex_real)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.spectralS_eq_complex_real.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.spatial_real))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.spatial_real)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.spatial_real.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.spectral_convolution))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.spectral_convolution)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.spectral_convolution.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.spatial_real_integrable))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.spatial_real_integrable)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.spatial_real_integrable.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.actual_spectral_square))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.actual_spectral_square)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.actual_spectral_square.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.weighted_integrableOn))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.weighted_integrableOn)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.weighted_integrableOn.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.endpoint_phase))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.endpoint_phase)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.endpoint_phase.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.endpoint_square_factor))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.endpoint_square_factor)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.endpoint_square_factor.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.actual_spectral_endpoint))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.actual_spectral_endpoint)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.actual_spectral_endpoint.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.original_test_endpoint))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.original_test_endpoint)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.original_test_endpoint.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.original_test_ac))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.original_test_ac)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.original_test_ac.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.actual_fullR_eq_original_J))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.actual_fullR_eq_original_J)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.actual_fullR_eq_original_J.__information_unit
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
    (family : DependentFamily.Registration arena (type_of% @OriginalActualSpectralEndpoint.spectral_correlation_convolution))
    (selection : Contract.SourceSelection) =>
  (show Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@OriginalActualSpectralEndpoint.spectral_correlation_convolution)
      (DependentFamily.Realization arena.signature) Unit Unit from {
    unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualSpectralEndpoint.spectral_correlation_convolution.__information_unit
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
