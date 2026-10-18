import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

namespace AtSkeleton

abbrev signature : Signature where
  Params := ReadPosition
  State _ := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p T => T.addressAt p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => some 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (T : ReadTree) (p : ReadPosition), T.paritySkeleton.addressAt p = (R.readout () p T).map (fun t => t % 2)

private theorem actual_law : arena.Law actual := @ReadTree.addressAt_skeleton

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (.leaf none) []
  norm_num [rejected, realize, ReadTree.paritySkeleton, ReadTree.addressAt] at hb

def evidence : Registration arena (type_of% (@ReadTree.addressAt_skeleton)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨[], .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    simp [actual, realize, ReadTree.addressAt]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.addressAt_skeleton)
    (type_of% (realize signature (fun _ p T => T.addressAt p) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.AtSkeleton.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.AtSkeleton.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p T => T.addressAt p) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature,
    definition := none,
    coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end AtSkeleton

namespace RelabelHeight

abbrev signature : Signature where
  Params := Unit
  State _ := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.height) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (f : ℤ → ℤ) (T : ReadTree), (T.relabelPotentialAddresses f).height = R.readout () () T

private theorem actual_law : arena.Law actual := @ReadTree.relabel_height

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h id (.leaf none)
  norm_num [rejected, realize, ReadTree.relabelPotentialAddresses, ReadTree.height] at hb

def evidence : Registration arena (type_of% (@ReadTree.relabel_height)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨(), .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    simp [actual, realize, ReadTree.height]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.relabel_height)
    (type_of% (realize signature (fun _ _ T => T.height) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.RelabelHeight.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.RelabelHeight.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ T => T.height) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "arg"],
      stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end RelabelHeight

namespace RelabelAddresses

abbrev signature : Signature where
  Params := Unit
  State _ := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.addresses) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (f : ℤ → ℤ) (T : ReadTree), (T.relabelPotentialAddresses f).addresses = (R.readout () () T).image f

private theorem actual_law : arena.Law actual := @ReadTree.relabel_addresses

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h id (.read 0 (.leaf none) (.leaf none))
  simp [rejected, realize, ReadTree.relabelPotentialAddresses, ReadTree.addresses] at hb

def evidence : Registration arena (type_of% (@ReadTree.relabel_addresses)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨(), .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    simp [actual, realize, ReadTree.addresses]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.relabel_addresses)
    (type_of% (realize signature (fun _ _ T => T.addresses) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.RelabelAddresses.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.RelabelAddresses.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ T => T.addresses) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "arg", "arg"],
      stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end RelabelAddresses

namespace AtRelabel

abbrev signature : Signature where
  Params := ReadPosition
  State _ := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p T => T.addressAt p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => some 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (f : ℤ → ℤ) (T : ReadTree) (p : ReadPosition), (T.relabelPotentialAddresses f).addressAt p = (R.readout () p T).map f

private theorem actual_law : arena.Law actual := @ReadTree.addressAt_relabel

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h id (.leaf none) []
  norm_num [rejected, realize, ReadTree.relabelPotentialAddresses, ReadTree.addressAt] at hb

def evidence : Registration arena (type_of% (@ReadTree.addressAt_relabel)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨[], .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    simp [actual, realize, ReadTree.addressAt]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.addressAt_relabel)
    (type_of% (realize signature (fun _ p T => T.addressAt p) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.AtRelabel.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.AtRelabel.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p T => T.addressAt p) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature,
    definition := none,
    coordinates := #[2],
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end AtRelabel

namespace AtInAddresses

abbrev signature : Signature where
  Params := Unit
  State _ := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.addresses) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (T : ReadTree) (p : ReadPosition) (t : ℤ), T.addressAt p = some t → t ∈ R.readout () () T

private theorem actual_law : arena.Law actual := @ReadTree.addressAt_in_addresses

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (.read 0 (.leaf none) (.leaf none)) [] 0 rfl
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@ReadTree.addressAt_in_addresses)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨(), .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    simp [actual, realize, ReadTree.addresses]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.addressAt_in_addresses)
    (type_of% (realize signature (fun _ _ T => T.addresses) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.AtInAddresses.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.AtInAddresses.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ T => T.addresses) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end AtInAddresses

namespace AddressCard

abbrev signature : Signature where
  Params := Unit
  State _ := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.potentialReadCount) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (T : ReadTree), T.addresses.card ≤ R.readout () () T

private theorem actual_law : arena.Law actual := @ReadTree.addresses_card_le_readCount

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (.read 0 (.leaf none) (.leaf none))
  norm_num [rejected, realize, ReadTree.addresses] at hb

def evidence : Registration arena (type_of% (@ReadTree.addresses_card_le_readCount)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨(), .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    simp [actual, realize, ReadTree.potentialReadCount]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.addresses_card_le_readCount)
    (type_of% (realize signature (fun _ _ T => T.potentialReadCount) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.AddressCard.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.AddressCard.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ T => T.potentialReadCount) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end AddressCard

namespace CountHeight

abbrev signature : Signature where
  Params := Unit
  State _ := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.height) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (T : ReadTree), T.potentialReadCount + 1 ≤ 2 ^ R.readout () () T

private theorem actual_law : arena.Law actual := @ReadTree.readCount_height_bound

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (.read 0 (.leaf none) (.leaf none))
  norm_num [rejected, realize, ReadTree.potentialReadCount] at hb

def evidence : Registration arena (type_of% (@ReadTree.readCount_height_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨(), .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    simp [actual, realize, ReadTree.height]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.readCount_height_bound)
    (type_of% (realize signature (fun _ _ T => T.height) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.CountHeight.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.CountHeight.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ T => T.height) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end CountHeight

namespace SkeletonRelabel

abbrev signature : Signature where
  Params := Unit
  State _ := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ReadTree
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.paritySkeleton) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .leaf none) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (f : ℤ → ℤ) (T : ReadTree), (∀ t ∈ T.addresses, f t % 2 = t % 2) → (T.relabelPotentialAddresses f).paritySkeleton = R.readout () () T

private theorem actual_law : arena.Law actual := @ReadTree.skeleton_relabel

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h id (.read 0 (.leaf none) (.leaf none)) (fun _ _ => rfl)
  simp [rejected, realize, ReadTree.relabelPotentialAddresses, ReadTree.paritySkeleton] at hb

def evidence : Registration arena (type_of% (@ReadTree.skeleton_relabel)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨(), .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    simp [actual, realize, ReadTree.paritySkeleton]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.skeleton_relabel)
    (type_of% (realize signature (fun _ _ T => T.paritySkeleton) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.SkeletonRelabel.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.SkeletonRelabel.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ T => T.paritySkeleton) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "arg"],
      stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end SkeletonRelabel

namespace ObservationLaw

open MeasureTheory

abbrev signature : Signature where
  Params := Bool
  State _ := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := SourcePoint → Observation
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ j T s => observation j s.1 T s.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => ⟨.a false, some (.a false), true, 0⟩) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (j : Bool) (T T' : ReadTree), SameSignature j T T' → ∀ β : Bias,
    (sourceLaw β).map (fun s => observation j s.1 T s.2) =
      (sourceLaw β).map (R.readout () j T')

private theorem actual_law : arena.Law actual := same_signature_observation_law

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hs : SameSignature false (.leaf none) (.leaf none) := ⟨rfl, fun _ _ _ => Iff.rfl⟩
  have hb := h false (.leaf none) (.leaf none) hs β
  have hE : MeasurableSet {z : Observation | z.output = none} := (Set.to_countable _).measurableSet
  have hx := congrArg (fun μ : Measure Observation => μ {z : Observation | z.output = none}) hb
  dsimp only [rejected, realize] at hx
  rw [Measure.map_apply (measurable_observation false (.leaf none)) hE,
    Measure.map_apply measurable_const hE] at hx
  simpa [rejected, realize, observation, ReadTree.run, Set.preimage] using hx

def evidence : Registration arena (type_of% (@same_signature_observation_law)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨false, .leaf none, .leaf (some (.a false)), ?_⟩
    intro he
    have hx := congrArg (fun f : SourcePoint → Observation => (f (false, fun _ => false)).output) he
    simp [actual, realize, observation, ReadTree.run] at hx

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@same_signature_observation_law)
    (type_of% (realize signature (fun _ j T s => observation j s.1 T s.2) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.ObservationLaw.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature.ObservationLaw.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ j T s => observation j s.1 T s.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end ObservationLaw

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature
