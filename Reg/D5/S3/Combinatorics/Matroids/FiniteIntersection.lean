import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Matroids.FiniteIntersection

/-! Source-bound observation of the first attaining-cut rank. -/

namespace Reg.D5.S3.Combinatorics.Matroids.FiniteIntersection

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids.FiniteIntersection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set Matroid

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State α := Matroid α
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ α := Set α → ℕ∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ M => M.eRk) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {α : Type u} (E : Set α) (_hE : E.Finite) (M₁ M₂ : Matroid α)
    (_h₁ : M₁.E = E) (_h₂ : M₂.E = E),
    (∃ I X : Set α, I ⊆ E ∧ X ⊆ E ∧ M₁.Indep I ∧ M₂.Indep I ∧
      I.ncard = (r.readout () α M₁ X).toNat + (M₂.eRk (E \ X)).toNat) ∧
    (∀ J Y : Set α, M₁.Indep J → M₂.Indep J →
      J.ncard ≤ (M₁.eRk Y).toNat + (M₂.eRk (E \ Y)).toNat)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨⟨I, X, hI, _hX, _hI₁, _hI₂, heq⟩, _⟩ :=
    h (α := PUnit.{u+1}) ∅ finite_empty (loopyOn ∅) (loopyOn ∅) rfl rfl
  have hI0 : I = ∅ := subset_empty_iff.mp hI
  subst I
  norm_num [rejected, realize, eRk_loopyOn] at heq

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, loopyOn {ULift.up ()}, freeOn {ULift.up ()}, ?_⟩
  intro h
  have hh := congrFun h ({ULift.up ()} : Set (ULift.{u} Unit))
  change (loopyOn {ULift.up ()}).eRk {ULift.up ()} =
    (freeOn {ULift.up ()}).eRk {ULift.up ()} at hh
  rw [eRk_loopyOn, eRk_freeOn subset_rfl, encard_singleton] at hh
  exact zero_ne_one hh

def source_registration : Registration arena.{u}
    (type_of% (@finite_matroid_intersection.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_matroid_intersection, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@finite_matroid_intersection.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.FiniteIntersection.finite_matroid_intersection.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.FiniteIntersection.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.FiniteIntersection
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg",
        "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Matroids.FiniteIntersection
