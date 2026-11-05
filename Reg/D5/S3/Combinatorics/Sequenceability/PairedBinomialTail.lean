import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Sequenceability.PairedBinomialTail

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail
open scoped BigOperators
noncomputable section

namespace density_pos
abbrev signature : DependentFamily.Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ r j => density r j) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {r j : ℕ}, j ≤ r → 0 < R.readout () r j

abbrev sourceScope := type_of% (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_pos)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := @_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_pos

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 0) (j := 0) (by decide)
  norm_num [rejected, DependentFamily.realize] at hh

private theorem dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  norm_num [actual, DependentFamily.realize, density, Nat.choose,
    Finset.sum_Icc_succ_top, Finset.sum_range_succ] <;> decide +revert

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_pos) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_pos.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_pos.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature (fun _ r j => density r j) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end density_pos

namespace density_symm
abbrev signature : DependentFamily.Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ r j => density r j) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {r j : ℕ}, j ≤ r → density r (r-j) = R.readout () r j

abbrev sourceScope := type_of% (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_symm)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := @_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_symm

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 0) (j := 0) (by decide)
  norm_num [rejected, DependentFamily.realize, density, Nat.choose] at hh

private theorem dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  norm_num [actual, DependentFamily.realize, density, Nat.choose,
    Finset.sum_Icc_succ_top, Finset.sum_range_succ] <;> decide +revert

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_symm) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_symm.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_symm.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature (fun _ r j => density r j) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end density_symm

namespace density_step
abbrev signature : DependentFamily.Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ r j => density r (j+1)) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {r j : ℕ}, j < r → R.readout () r j = density r j * (2*(j:ℚ)+1) / (2*(r:ℚ)-2*j-1)

abbrev sourceScope := type_of% (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_step)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := @_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_step

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 1) (j := 0) (by decide)
  norm_num [rejected, DependentFamily.realize, density, Nat.choose] at hh

private theorem dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  norm_num [actual, DependentFamily.realize, density, Nat.choose,
    Finset.sum_Icc_succ_top, Finset.sum_range_succ] <;> decide +revert

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_step) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_step.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_step.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature (fun _ r j => density r (j+1)) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end density_step

namespace density_middle_le
abbrev signature : DependentFamily.Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ r j => density r j) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {r j : ℕ}, 6 ≤ r → 3 ≤ j → j ≤ r-3 → R.readout () r j ≤ density r 3

abbrev sourceScope := type_of% (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_middle_le)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := @_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_middle_le

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 6) (j := 3) (by decide) (by decide) (by decide)
  norm_num [rejected, DependentFamily.realize, density, Nat.choose] at hh

private theorem dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  norm_num [actual, DependentFamily.realize, density, Nat.choose,
    Finset.sum_Icc_succ_top, Finset.sum_range_succ] <;> decide +revert

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_middle_le) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_middle_le.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_middle_le.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature (fun _ r j => density r j) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end density_middle_le

namespace density_two
abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ r => density r 2) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {r : ℕ}, 2 ≤ r → R.readout () () r = 3 / ((2*(r:ℚ)-1)*(2*r-3))

abbrev sourceScope := type_of% (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_two)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := @_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_two

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 2) (by decide)
  norm_num [rejected, DependentFamily.realize] at hh

private theorem dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  norm_num [actual, DependentFamily.realize, density, Nat.choose,
    Finset.sum_Icc_succ_top, Finset.sum_range_succ] <;> decide +revert

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_two) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_two.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_two.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature (fun _ _ r => density r 2) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail
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
  options := #[]
end density_two

namespace density_three
abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ r => density r 3) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {r : ℕ}, 3 ≤ r → R.readout () () r = 15 / ((2*(r:ℚ)-1)*(2*r-3)*(2*r-5))

abbrev sourceScope := type_of% (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_three)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := @_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_three

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 3) (by decide)
  norm_num [rejected, DependentFamily.realize] at hh

private theorem dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 3, 4, ?_⟩
  norm_num [actual, DependentFamily.realize, density, Nat.choose,
    Finset.sum_Icc_succ_top, Finset.sum_range_succ] <;> decide +revert

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_three) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_three.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_three.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature (fun _ _ r => density r 3) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail
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
  options := #[]
end density_three

namespace density_tail_le
abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ r => ∑ j ∈ Finset.Icc 2 (r-2), density r j) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {r : ℕ}, 6 ≤ r → R.readout () () r ≤ 2*density r 2 + (r-5:ℕ)*density r 3

abbrev sourceScope := type_of% (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_tail_le)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := @_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_tail_le

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 6) (by decide)
  norm_num [rejected, DependentFamily.realize, density, Nat.choose] at hh

private theorem dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 6, ?_⟩
  have hIcc : Finset.Icc (2 : ℕ) 4 = {2, 3, 4} := by decide
  norm_num [actual, DependentFamily.realize, density, hIcc, Nat.choose]

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_tail_le) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_tail_le.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.density_tail_le.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature (fun _ _ r => ∑ j ∈ Finset.Icc 2 (r-2), density r j) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail
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
  options := #[]
end density_tail_le

namespace paired_tail_bound
abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ r => (r:ℚ) * ∑ j ∈ Finset.Icc 2 (r-2), density r j) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {r : ℕ}, 6 ≤ r → R.readout () () r ≤ (r:ℚ)*(27*r-105) / ((2*r-1)*(2*r-3)*(2*r-5))

abbrev sourceScope := type_of% (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.paired_tail_bound)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := @_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.paired_tail_bound

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 6) (by decide)
  norm_num [rejected, DependentFamily.realize] at hh

private theorem dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 6, ?_⟩
  have hIcc : Finset.Icc (2 : ℕ) 4 = {2, 3, 4} := by decide
  norm_num [actual, DependentFamily.realize, density, hIcc, Nat.choose]

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.paired_tail_bound) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.paired_tail_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail.paired_tail_bound.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature (fun _ _ r => (r:ℚ) * ∑ j ∈ Finset.Icc 2 (r-2), density r j) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.PairedBinomialTail
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
  options := #[]
end paired_tail_bound

end
end Reg.D5.S3.Combinatorics.Sequenceability.PairedBinomialTail
