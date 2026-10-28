import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization

/-! # Source-bound classification of strictly positive five-mode networks -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.ConstraintRelations.RationalZeroRealization
open _root_.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape

noncomputable section
attribute [local instance] Classical.propDecidable

def signature : DependentFamily.Signature where
  Params := Σ n : Nat, Σ m : Nat, Σ k : Nat, Network n m k
  State p := Fin p.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ p a => p.2.2.2.law a) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ (n : Nat) (P : (Fin n → Bool) → ℚ),
    (∀ a, 0 ≤ P a) → (∑ a, P a = 1) →
    ((∃ m k : Nat, ∃ net : Network n m k,
      (∀ j, Strict (net.factor j).table) ∧ 0 < net.partition ∧
        ∀ a, R.readout () ⟨n, m, k, net⟩ a = P a) ↔
      ∃ K : LoopGraph n, ∀ a, 0 < P a ↔ Independent K a)

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.result)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := source_bridge.mp
  _root_.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.result

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : ℚ)) (fun e => nomatch e)

def delta : (Fin 1 → Bool) → ℚ := fun a => if a = (fun _ => false) then 1 else 0

def loop : LoopGraph 1 where
  edge _ _ := True
  symm := by intros; trivial

theorem delta_nonneg : ∀ a, 0 ≤ delta a := by
  intro a; unfold delta; split <;> norm_num

theorem delta_sum : ∑ a, delta a = 1 := by classical simp [delta]

theorem delta_support : ∀ a, 0 < delta a ↔ Independent loop a := by
  intro a
  have hi : Independent loop a ↔ a = (fun _ => false) := by
    constructor
    · intro h
      have hz := h 0 0 trivial
      have hb : a 0 = false := by cases hv : a 0 <;> simpa [hv] using hz
      funext i
      have he : i = 0 := Subsingleton.elim _ _
      simpa [he] using hb
    · intro h
      subst a
      intro i j _; rfl
  rw [hi]
  by_cases ha : a = (fun _ => false) <;> simp [delta, ha]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨m, k, net, _, _, hl⟩ :=
    (h 1 delta delta_nonneg delta_sum).mpr ⟨loop, delta_support⟩
  have hf := hl (fun _ => false)
  change (0 : ℚ) = delta (fun _ => false) at hf
  norm_num [delta] at hf

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    obtain ⟨m, k, net, _, _, hl⟩ :=
      (_root_.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.result
        1 delta delta_nonneg delta_sum).mpr ⟨loop, delta_support⟩
    refine ⟨⟨1, m, k, net⟩, (fun _ => false), (fun _ => true), ?_⟩
    change net.law (fun _ => false) ≠ net.law (fun _ => true)
    rw [hl, hl]
    norm_num [delta, funext_iff]

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@_root_.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.result)
      (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ p a => p.2.2.2.law a) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization
    definition := none
    coordinates := #[0, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg",
        "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

namespace PinStrict

abbrev signature : DependentFamily.Signature where
  Params := Table
  State _ := Triple
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ T t => T.val t) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ t : Triple,
    _root_.D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary.A ![t.1,t.2.1,t.2.2] →
      0 < R.readout () pinTable t

abbrev sourceScope := type_of% (@pin_strict)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl
theorem actual_positive : arena.Law actual := source_bridge.mp pin_strict

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : ℚ)) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (false,false,false) (by simp [_root_.D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary.A])
  change (0 : ℚ) < 0 at hh
  exact (lt_irrefl 0) hh

theorem dependence : ∀ i : Unit, ∃ (p : signature.Params) (s t : signature.State p),
    actual.readout i p s ≠ actual.readout i p t := by
  intro i
  refine ⟨pinTable,(false,false,false),(true,true,true),?_⟩
  change pinTable.val _ ≠ pinTable.val _
  norm_num [pinTable,pinRaw,_root_.D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary.A]

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@_root_.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.pin_strict)
      (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.pin_strict.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.PinStrict.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature (fun _ T t => T.val t) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization
    definition := some {
      owner := `D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization
      name := `D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.Strict
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration
end PinStrict

namespace Necessity

abbrev signature : DependentFamily.Signature where
  Params := Σ n : Nat, Σ m : Nat, Σ k : Nat, Network n m k
  State p := Fin p.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ p a => p.2.2.2.law a) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {n m k : Nat} (net : Network n m k)
    (hs : ∀ j, Strict (net.factor j).table),
    0 < net.partition ∧ ∀ a,
      0 < R.readout () ⟨n,m,k,net⟩ a ↔ Independent (induced net) a

abbrev sourceScope := type_of% (@necessity)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl
theorem actual_positive : arena.Law actual := source_bridge.mp (@necessity)

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : ℚ)) (fun e => nomatch e)

def emptyNet : Network 0 0 0 := ⟨fun i => Fin.elim0 i⟩

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : ∀ j, Strict (emptyNet.factor j).table := fun j => Fin.elim0 j
  have hi : Independent (induced emptyNet) (fun _ => false) := by
    intro i; exact Fin.elim0 i
  have hh := ((h emptyNet hs).2 (fun _ => false)).mpr hi
  change (0 : ℚ) < 0 at hh
  exact (lt_irrefl 0) hh

def pinNet : Network 1 0 1 := ⟨fun _ => ⟨(.inl 0,.inl 0,.inl 0),pinTable⟩⟩

theorem dependence : ∀ i : Unit, ∃ (p : signature.Params) (s t : signature.State p),
    actual.readout i p s ≠ actual.readout i p t := by
  intro i
  refine ⟨⟨1,0,1,pinNet⟩,(fun _ => false),(fun _ => true),?_⟩
  change pinNet.law (fun _ => false) ≠ pinNet.law (fun _ => true)
  have hp := (necessity pinNet (fun _ => pin_strict)).1
  have hf : pinNet.marginal (fun _ => false) = 1/5 := by
    norm_num [pinNet, Network.marginal, Network.weight, Factor.value, pinTable,pinRaw,
      _root_.D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary.A]
  have ht : pinNet.marginal (fun _ => true) = 0 := by
    norm_num [pinNet, Network.marginal, Network.weight, Factor.value, pinTable,pinRaw,
      _root_.D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary.A]
  rw [Network.law,Network.law,hf,ht,zero_div]
  exact div_ne_zero (by norm_num) (ne_of_gt hp)

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@_root_.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.necessity)
      (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.necessity.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.Necessity.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature (fun _ p a => p.2.2.2.law a) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body","body","body","body","body","arg","body","fn","arg","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration
end Necessity

end
end Reg.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization
