import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Observer.RationalRouting.Prices

/-! Exact source-owned variation and dependence for actual rational acquisition. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.RationalRouting

noncomputable section
namespace Reg.D5.S3.Observer.RationalRouting.Views

abbrev signature : Signature where
  Params := View
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := ViewOutput V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ V x => originalView V x) Empty.elim

def rejected : Realization signature :=
  realize signature (fun _ V _ => originalView V 1) Empty.elim

theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨View.B,1,2,?_⟩
  change (1 : ℚ) ≠ 2
  norm_num

def arena : Arena where
  signature := signature
  Law R :=
    (∀ (p q : ℕ), 0 < p → 0 < q → p.Coprime q → encode (decodePair p q) = (p,q)) ∧
    (∀ w : List Bool, decodePair (encode w).1 (encode w).2 = w) ∧
    (∀ (V : View) (x : ℚ), 0 < x → recoverView V (R.readout () V x) = x) ∧
    (∀ w : List Bool, ratio (encode w) = attain w 1) ∧
    (∀ w : List Bool, originalWord (ratio (encode w)) = w)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h.2.2.1 View.B 2 (by norm_num)
  norm_num [rejected,realize,originalView,recoverView] at bad

def family : Registration arena (type_of% (@original_views_reconstruct)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_views_reconstruct,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_views_reconstruct) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.RationalRouting.original_views_reconstruct.__information_unit
  realizationName := `Reg.D5.S3.Observer.RationalRouting.Views.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ V x => originalView V x) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.RationalRouting.Views
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg","arg","fn","arg","body","body","body","fn","arg","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Observer.RationalRouting.Views
