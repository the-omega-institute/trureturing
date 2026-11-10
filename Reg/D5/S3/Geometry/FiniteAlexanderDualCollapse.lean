import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteAlexanderDualCollapse

noncomputable section
open Set Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteAlexanderDualCollapse
open _root_.D5.S3.Geometry.FiniteRelativeSimplicialCollapse

namespace Reg.D5.S3.Geometry.FiniteAlexanderDualCollapse
universe u_1
namespace Augmented
abbrev signature : Signature where
  Params := Type u_1
  State V := PreAbstractSimplicialComplex V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := Finset V → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1} :=
  realize signature (fun _ _ K s => AugmentedFace K s) Empty.elim
def rejected : Realization signature.{u_1} :=
  realize signature (fun _ _ _ _ => False) Empty.elim
abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {V : Type u_1} [fv : Fintype V] [dv : DecidableEq V]
    (W : Finset V) (K : PreAbstractSimplicialComplex V) (hp : Proper W K) (s : Finset V),
    R.readout () V (dual W K) s ↔ s ⊆ W ∧ ¬ AugmentedFace K (W \ s)
private theorem bridge : (type_of% (@dual_augmented.{u_1})) ↔ arena.{u_1}.Law actual := Iff.rfl
private theorem negative : ¬ arena.{u_1}.Law rejected := by
  intro h
  let W : Finset (ULift.{u_1} Unit) := {ULift.up ()}
  have hp : Proper W (⊥ : PreAbstractSimplicialComplex (ULift.{u_1} Unit)) := by
    change ¬ (W = ∅ ∨ False)
    simp [W]
  have bad := (@h (ULift.{u_1} Unit) inferInstance inferInstance W ⊥ hp ∅).mpr
    ⟨empty_subset _, by simpa only [Proper, Finset.sdiff_empty] using hp⟩
  exact bad
private theorem dependence : ObservationalDependence signature.{u_1} actual := by
  intro i
  refine ⟨ULift.{u_1} Unit, ⊥, ⊤, ?_⟩
  intro h
  have hh := congrFun h ({ULift.up ()} : Finset (ULift.{u_1} Unit))
  change (({ULift.up ()} : Finset (ULift.{u_1} Unit)) = ∅ ∨ False) =
    (({ULift.up ()} : Finset (ULift.{u_1} Unit)) = ∅ ∨
      ({ULift.up ()} : Finset (ULift.{u_1} Unit)).Nonempty) at hh
  have bad := Eq.mpr hh (Or.inr (Finset.singleton_nonempty (ULift.up ())))
  exact bad.elim (fun he => Finset.singleton_ne_empty _ he) id

def family : Registration arena.{u_1} (type_of% (@dual_augmented.{u_1})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@dual_augmented.{u_1}), rejected, negative⟩
  sensitivity := ⟨fun _i => ⟨rejected, fun _j h => (h (Subsingleton.elim _ _)).elim, rfl,
    negative⟩, fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@dual_augmented.{u_1}) (Realization signature.{u_1}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteAlexanderDualCollapse.Augmented.unit
  realizationName := `Reg.D5.S3.Geometry.FiniteAlexanderDualCollapse.Augmented.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K s => AugmentedFace K s) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteAlexanderDualCollapse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Augmented
end Reg.D5.S3.Geometry.FiniteAlexanderDualCollapse
