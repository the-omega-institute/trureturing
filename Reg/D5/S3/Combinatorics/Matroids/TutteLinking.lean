import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Matroids.TutteLinking

/-! Source-bound observation of the terminal rank in Tutte linking. -/

namespace Reg.D5.S3.Combinatorics.Matroids.TutteLinking

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids.TutteLinking
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set Matroid

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State E := Matroid E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ E := Set E → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ M => rk M) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ (E : Type u) [Finite E] (M : Matroid E) (S T : Set E),
    S ⊆ M.E → T ⊆ M.E → Disjoint S T →
    ∃ C : Set E, C ⊆ M.E \ (S ∪ T) ∧
      let D : Set E := (M.E \ (S ∪ T)) \ C
      let N : Matroid E := (M ／ C) ＼ D
      N.E = S ∪ T ∧
        r.readout () E N S + rk N T - rk N (S ∪ T) = kappa M S T

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨C, hC, hNE, heq⟩ := h (ULift.{u} Unit) (loopyOn ∅) ∅ ∅
    (by simp) (by simp) (by simp)
  have hC0 : C = ∅ := subset_empty_iff.mp (by simpa using hC)
  subst C
  have hk : kappa (loopyOn (∅ : Set (ULift.{u} Unit))) ∅ ∅ = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply csInf_le (OrderBot.bddBelow _)
    refine ⟨∅, by simp, by simp, ?_⟩
    simp [cut, rk]
  rw [hk] at heq
  norm_num [rejected, realize, rk] at heq

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, loopyOn {ULift.up ()}, freeOn {ULift.up ()}, ?_⟩
  intro h
  have hh := congrFun h ({ULift.up ()} : Set (ULift.{u} Unit))
  change rk (loopyOn {ULift.up ()}) {ULift.up ()} =
    rk (freeOn {ULift.up ()}) {ULift.up ()} at hh
  norm_num [rk, eRk_loopyOn, eRk_freeOn subset_rfl, encard_singleton] at hh

def source_registration : Registration arena.{u}
    (type_of% (@tutte_linking.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tutte_linking, rejected, rejected_law⟩
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
      (@tutte_linking.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.TutteLinking.tutte_linking.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.TutteLinking.source_registration
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
    owner := `D5.S3.Combinatorics.Matroids.TutteLinking
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Matroids.TutteLinking
