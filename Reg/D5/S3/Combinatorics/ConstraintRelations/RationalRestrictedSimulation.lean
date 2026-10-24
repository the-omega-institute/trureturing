import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation

/-! # Full source families for local and network restricted simulation -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation

open _root_.D5.S3.Combinatorics.ConstraintRelations
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.ConstraintRelations.RationalZeroRealization
open _root_.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization
open _root_.D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation
open _root_.D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Local

structure Parameters where
  V : Type
  factor : Factor V
  strict : Strict factor.table

abbrev signature : DependentFamily.Signature where
  Params := Parameters
  State p := p.V → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def observe (p : Parameters) (b : p.V → Bool) : ℚ :=
  ∑ h : Bool → Bool, ∏ i,
    (localExtension p.factor p.strict i).value
      (Sum.elim b (Sum.elim (fun _ : Unit => false) h))

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ p b => observe p b) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {V : Type} (f : Factor V) (hf : Strict f.table),
    (∀ i, Restricted (localExtension f hf i).table) ∧
    0 < localScale f.table hf ∧
    ∀ b : V → Bool,
      R.readout () ⟨V,f,hf⟩ b = localScale f.table hf * f.value b

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation.local_simulation)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := source_bridge.mp (@local_simulation)

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : ℚ)) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let f : Factor Unit := ⟨((),(),()),pinTable⟩
  have hf : Strict f.table := pin_strict
  have hh := (h f hf).2.2 (fun _ => false)
  change (0 : ℚ) = localScale f.table hf * f.value (fun _ => false) at hh
  have hp := (local_simulation f hf).2.1
  have hv : f.value (fun _ => false) = 1/5 := by norm_num [f,Factor.value,pinTable,pinRaw,A]
  rw [hv] at hh
  linarith

theorem dependence : ∀ i : Unit, ∃ (p : signature.Params) (s t : signature.State p),
    actual.readout i p s ≠ actual.readout i p t := by
  intro i
  let f : Factor Unit := ⟨((),(),()),pinTable⟩
  have hf : Strict f.table := pin_strict
  refine ⟨⟨Unit,f,hf⟩,(fun _ => false),(fun _ => true),?_⟩
  change observe ⟨Unit,f,hf⟩ (fun _ => false) ≠ observe ⟨Unit,f,hf⟩ (fun _ => true)
  change (∑ h : Bool → Bool, ∏ j, (localExtension f hf j).value
    (Sum.elim (fun _ => false) (Sum.elim (fun _ : Unit => false) h))) ≠
    (∑ h : Bool → Bool, ∏ j, (localExtension f hf j).value
    (Sum.elim (fun _ => true) (Sum.elim (fun _ : Unit => false) h)))
  rw [(local_simulation f hf).2.2, (local_simulation f hf).2.2]
  have hp := (local_simulation f hf).2.1
  have hv : f.value (fun _ => false) = 1/5 := by
    norm_num [f, Factor.value, pinTable, pinRaw, A]
  have ht : f.value (fun _ => true) = 0 := by
    norm_num [f, Factor.value, pinTable, pinRaw, A]
  rw [hv, ht, mul_zero]
  exact mul_ne_zero (ne_of_gt hp) (by norm_num)

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
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@_root_.D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation.local_simulation)
      (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation.local_simulation.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation.Local.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature (fun _ p b => observe p b) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body","body","body","arg","arg","body","fn","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration
end Local

namespace Network

abbrev signature : DependentFamily.Signature where
  Params := Σ n : Nat, Σ m : Nat, Σ k : Nat, RationalZeroRealization.Network n m k
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
  Law R := ∀ (n m k : Nat) (net : Network n m k)
    (hs : ∀ j, Strict (net.factor j).table),
    Function.Injective (numberedEmbedding (n := n) (m := m) (k := k)) ∧
    (∀ i : Fin n, numberedEmbedding (m := m) (k := k) (.inl i) = .inl i) ∧
    (∀ (b : Fin n ⊕ Fin m → Bool) (h : Unit ⊕ (Fin k × Bool) → Bool)
      (v : Fin n ⊕ Fin m), numberedAssignment b h (numberedEmbedding v) = b v) ∧
    (∀ j : Fin k, ((replacement net hs).factor
      (Fintype.equivFin (ReplacementIndex k) (.inr (j, .inl ())))).scope =
      (numberedEmbedding (net.factor j).scope.1,
        numberedEmbedding (net.factor j).scope.2.1,
        numberedEmbedding (net.factor j).scope.2.2)) ∧
    (∀ i, Restricted ((replacement net hs).factor i).table) ∧
    0 < replacementScale net hs ∧
    (∀ b : Fin n ⊕ Fin m → Bool,
      (∑ h : Unit ⊕ (Fin k × Bool) → Bool, ∏ i,
        ((replacement net hs).factor i).value (numberedAssignment b h)) =
        replacementScale net hs * ∏ j, (net.factor j).value b) ∧
    0 < net.partition ∧ 0 < (replacement net hs).partition ∧
    (∀ a, (replacement net hs).marginal a = replacementScale net hs * net.marginal a) ∧
    (replacement net hs).partition = replacementScale net hs * net.partition ∧
    (∀ a, R.readout () ⟨n, Fintype.card (ReplacementHidden m k),
      Fintype.card (ReplacementIndex k), replacement net hs⟩ a = R.readout () ⟨n, m, k, net⟩ a)

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation.result)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := source_bridge.mp result

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun _ p _ => if p.2.1 = 0 then (1 : ℚ) else 0) (fun e => nomatch e)

def empty : RationalZeroRealization.Network 0 0 0 := ⟨fun i => Fin.elim0 i⟩

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : ∀ j, Strict (empty.factor j).table := fun j => Fin.elim0 j
  rcases h 0 0 0 empty hs with ⟨_, _, _, _, _, _, _, _, _, _, _, hl⟩
  have hh := hl (fun i => Fin.elim0 i)
  change (if Fintype.card (ReplacementHidden 0 0) = 0 then (1 : ℚ) else 0) = 1 at hh
  norm_num [ReplacementHidden] at hh

def pinNet : RationalZeroRealization.Network 1 0 1 :=
  ⟨fun _ => ⟨(.inl 0, .inl 0, .inl 0), pinTable⟩⟩

theorem dependence : ∀ i : Unit, ∃ (p : signature.Params) (s t : signature.State p),
    actual.readout i p s ≠ actual.readout i p t := by
  intro i
  refine ⟨⟨1, 0, 1, pinNet⟩, (fun _ => false), (fun _ => true), ?_⟩
  change pinNet.law (fun _ => false) ≠ pinNet.law (fun _ => true)
  have hp := (necessity pinNet (fun _ => pin_strict)).1
  have hf : pinNet.marginal (fun _ => false) = 1 / 5 := by
    norm_num [pinNet, RationalZeroRealization.Network.marginal,
      RationalZeroRealization.Network.weight, Factor.value, pinTable, pinRaw, A]
  have ht : pinNet.marginal (fun _ => true) = 0 := by
    norm_num [pinNet, RationalZeroRealization.Network.marginal,
      RationalZeroRealization.Network.weight, Factor.value, pinTable, pinRaw, A]
  rw [RationalZeroRealization.Network.law, RationalZeroRealization.Network.law, hf, ht,
    zero_div]
  exact div_ne_zero (by norm_num) (ne_of_gt hp)

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
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@_root_.D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation.result)
      (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation.Network.familyRegistration
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
    owner := `D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body","body","body","body","body","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","body","fn","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","body","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration
end Network

end
end Reg.D5.S3.Combinatorics.ConstraintRelations.RationalRestrictedSimulation
