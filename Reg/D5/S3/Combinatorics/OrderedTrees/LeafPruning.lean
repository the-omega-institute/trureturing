import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.OrderedTrees.LeafPruning

/-! Source-bound audits of ordered-tree pruning and decoration. -/

open _root_.D5.S3.Combinatorics.OrderedTrees.LeafPruning
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.SingleDependentReadout (sensitivity)
set_option autoImplicit false

private def forkDecoration : Decoration :=
  .branch 0 (.tip 0) (.more 0 (.tip 0) (.last 0))

private theorem forkDecoration_matches :
    forkDecoration.inflate.height = forkDecoration.inflate.internal := by
  apply (height_eq_internal_iff_fork _).mpr
  refine ⟨(decorationEquiv forkDecoration).property, 0, 0, 0, Or.inl rfl, ?_⟩
  rw [inflate_prune]
  rfl

private theorem count_five_ne_zero : count 5 ≠ 0 := by
  rw [(count_spec 5).2]
  apply ne_of_gt
  apply (Set.ncard_pos (count_spec 5).1).2
  refine ⟨forkDecoration.inflate, ?_, forkDecoration_matches⟩
  simp [forkDecoration, Decoration.inflate, DecorationForest.inflate_forest,
    Tree.vertices, Forest.forest_vertices] <;> rfl

namespace Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.CountSpec

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => count x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    Set.Finite {t : Tree | t.vertices = n ∧ t.height = t.internal} ∧
      R.readout () () n = Set.ncard {t : Tree | t.vertices = n ∧ t.height = t.internal}

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 5).2
  change 0 = Set.ncard {t : Tree | t.vertices = 5 ∧ t.height = t.internal} at he
  exact count_five_ne_zero (((count_spec 5).2).trans he.symm)

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 5, ?_⟩
  change count 0 ≠ count 5
  rw [count_eq_zero_of_lt_five 0 (by decide)]
  exact count_five_ne_zero.symm

def sourceRegistration :
    Registration arena
      (type_of% @D5.S3.Combinatorics.OrderedTrees.LeafPruning.count_spec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.OrderedTrees.LeafPruning.count_spec, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Combinatorics.OrderedTrees.LeafPruning.count_spec) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.OrderedTrees.LeafPruning.count_spec.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.CountSpec.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => count x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.OrderedTrees.LeafPruning
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.CountSpec

namespace Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.HeightInternal

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Tree) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => x.height) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ t : Tree, R.readout () () t = t.internal ↔
    t ≠ .node .nil ∧ t.prune.vertices = t.prune.height + 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : rejected.readout () () (path 0) = (path 0).internal := by
    change 0 = (path 0).internal
    simp [path, stem, Tree.internal]
  exact (h (path 0)).mp hzero |>.1 rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), path 0, path 1, ?_⟩
  change (path 0).height ≠ (path 1).height
  decide

def sourceRegistration :
    Registration arena
      (type_of% @D5.S3.Combinatorics.OrderedTrees.LeafPruning.height_eq_internal_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.OrderedTrees.LeafPruning.height_eq_internal_iff, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Combinatorics.OrderedTrees.LeafPruning.height_eq_internal_iff) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.OrderedTrees.LeafPruning.height_eq_internal_iff.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.HeightInternal.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x.height) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.OrderedTrees.LeafPruning
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.HeightInternal

namespace Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.ExcessOneFork

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Tree) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => x.vertices) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ t : Tree, R.readout () () t = t.height + 1 ↔
    ∃ b l r, (l = 0 ∨ r = 0) ∧ t = fork b l r

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have htwo : rejected.readout () () (path 0) = (path 0).height + 1 := rfl
  have hexcess := (excess_one_iff_fork (path 0)).mpr ((h (path 0)).mp htwo)
  exact (by decide : (path 0).vertices ≠ (path 0).height + 1) hexcess

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), path 0, path 1, ?_⟩
  change (path 0).vertices ≠ (path 1).vertices
  decide

def sourceRegistration :
    Registration arena
      (type_of% @D5.S3.Combinatorics.OrderedTrees.LeafPruning.excess_one_iff_fork) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.OrderedTrees.LeafPruning.excess_one_iff_fork, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Combinatorics.OrderedTrees.LeafPruning.excess_one_iff_fork) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.OrderedTrees.LeafPruning.excess_one_iff_fork.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.ExcessOneFork.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x.vertices) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.OrderedTrees.LeafPruning
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.ExcessOneFork

namespace Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.HeightInternalFork

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Tree) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => x.height) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ t : Tree, R.readout () () t = t.internal ↔ t ≠ .node .nil ∧
    ∃ b l r, (l = 0 ∨ r = 0) ∧ t.prune = fork b l r

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : rejected.readout () () (path 0) = (path 0).internal := by
    change 0 = (path 0).internal
    simp [path, stem, Tree.internal]
  exact (h (path 0)).mp hzero |>.1 rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), path 0, path 1, ?_⟩
  change (path 0).height ≠ (path 1).height
  decide

def sourceRegistration :
    Registration arena
      (type_of% @D5.S3.Combinatorics.OrderedTrees.LeafPruning.height_eq_internal_iff_fork) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.OrderedTrees.LeafPruning.height_eq_internal_iff_fork, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Combinatorics.OrderedTrees.LeafPruning.height_eq_internal_iff_fork) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.OrderedTrees.LeafPruning.height_eq_internal_iff_fork.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.HeightInternalFork.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x.height) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.OrderedTrees.LeafPruning
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.HeightInternalFork

namespace Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.SkeletonsSpec

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => (skeletons x).card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ u : ℕ,
    (∀ t : Tree, t ∈ skeletons u ↔ t.vertices = u + 3 ∧ t.vertices = t.height + 1) ∧
      R.readout () () u = 2 * u + 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact Nat.zero_ne_one (h 0).2

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change (skeletons 0).card ≠ (skeletons 1).card
  rw [(skeletons_spec 0).2, (skeletons_spec 1).2]
  decide

def sourceRegistration :
    Registration arena
      (type_of% @D5.S3.Combinatorics.OrderedTrees.LeafPruning.skeletons_spec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.OrderedTrees.LeafPruning.skeletons_spec, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Combinatorics.OrderedTrees.LeafPruning.skeletons_spec) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.OrderedTrees.LeafPruning.skeletons_spec.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.SkeletonsSpec.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => (skeletons x).card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.OrderedTrees.LeafPruning
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.SkeletonsSpec

namespace Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.InflatePrune

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Decoration) (fun _ => Tree)

def actual : Realization signature :=
  realize signature (fun _ _ x => x.inflate.prune) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => path 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ d : Decoration, R.readout () () d = d.skeleton

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (by decide : path 1 ≠ (Decoration.tip 0).skeleton) (h (.tip 0))

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), .tip 0, forkDecoration, ?_⟩
  change (Decoration.tip 0).inflate.prune ≠ forkDecoration.inflate.prune
  rw [inflate_prune, inflate_prune]
  decide

def sourceRegistration :
    Registration arena
      (type_of% @D5.S3.Combinatorics.OrderedTrees.LeafPruning.inflate_prune) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.OrderedTrees.LeafPruning.inflate_prune, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Combinatorics.OrderedTrees.LeafPruning.inflate_prune) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.OrderedTrees.LeafPruning.inflate_prune.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.InflatePrune.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x.inflate.prune) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.OrderedTrees.LeafPruning
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.InflatePrune

namespace Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.ActualCountCoordinates

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Tree) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => x.vertices) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (t : Tree), t.height = t.internal →
    ∃ d : Decoration, ∃ b l r : ℕ,
      d.inflate = t ∧ d.skeleton = fork b l r ∧ (l = 0 ∨ r = 0) ∧
        R.readout () () t = b + l + r + 5 + d.gapTotal ∧
        d.slots = 2 * (b + l + r) + 5

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨d, b, l, r, _, _, _, hsize, _⟩ := h forkDecoration.inflate forkDecoration_matches
  change 0 = b + l + r + 5 + d.gapTotal at hsize
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), path 0, path 1, ?_⟩
  change (path 0).vertices ≠ (path 1).vertices
  decide

def sourceRegistration :
    Registration arena
      (type_of% @D5.S3.Combinatorics.OrderedTrees.LeafPruning.actual_count_coordinates) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.OrderedTrees.LeafPruning.actual_count_coordinates, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Combinatorics.OrderedTrees.LeafPruning.actual_count_coordinates) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.OrderedTrees.LeafPruning.actual_count_coordinates.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.ActualCountCoordinates.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x.vertices) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.OrderedTrees.LeafPruning
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.ActualCountCoordinates

namespace Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.CountSmall

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => count x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, n < 5 → R.readout () () n = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact Nat.one_ne_zero (h 0 (by decide))

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 5, ?_⟩
  change count 0 ≠ count 5
  rw [count_eq_zero_of_lt_five 0 (by decide)]
  exact count_five_ne_zero.symm

def sourceRegistration :
    Registration arena
      (type_of% @D5.S3.Combinatorics.OrderedTrees.LeafPruning.count_eq_zero_of_lt_five) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.OrderedTrees.LeafPruning.count_eq_zero_of_lt_five, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Combinatorics.OrderedTrees.LeafPruning.count_eq_zero_of_lt_five) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.OrderedTrees.LeafPruning.count_eq_zero_of_lt_five.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.CountSmall.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => count x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.OrderedTrees.LeafPruning
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.CountSmall

namespace Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.DecorationWeight

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Decoration) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => x.slots) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (d : Decoration) (u : ℕ), d.skeleton ∈ skeletons u →
    d.inflate.vertices = u + 5 + d.gapTotal ∧ R.readout () () d = 2 * u + 5

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hm : forkDecoration.skeleton ∈ skeletons 0 := by decide
  exact (by decide : (0 : ℕ) ≠ 2 * 0 + 5) (h forkDecoration 0 hm).2

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), .tip 0, forkDecoration, ?_⟩
  change (Decoration.tip 0).slots ≠ forkDecoration.slots
  decide

def sourceRegistration :
    Registration arena
      (type_of% @D5.S3.Combinatorics.OrderedTrees.LeafPruning.decoration_weight) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.OrderedTrees.LeafPruning.decoration_weight, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Combinatorics.OrderedTrees.LeafPruning.decoration_weight) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.OrderedTrees.LeafPruning.decoration_weight.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.DecorationWeight.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x.slots) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.OrderedTrees.LeafPruning
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.OrderedTrees.LeafPruning.DecorationWeight
