import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation
import Reg.Support.DependentFamily

open scoped BigOperators
open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation

universe u
noncomputable section
namespace Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation

abbrev signature : Signature where
  Params := Σ α : Type u, Finset α → ℝ
  State p := Finset p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p S => p.2 S) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u}
    (U : Finset α) (w : α → ℝ) (hw : ∀ i ∈ U, 0 < w i)
    (f : Finset α → ℝ)
    (hf : ∀ S ⊆ U, ∀ T ⊆ U, S ⊆ T → f S ≤ f T)
    (k : ℕ) (hk : k < U.card),
    (∑ S ∈ U.powersetCard k, (∏ i ∈ S, w i) * f S) /
        (∑ S ∈ U.powersetCard k, ∏ i ∈ S, w i) ≤
    (∑ S ∈ U.powersetCard (k + 1), (∏ i ∈ S, w i) * R.readout () ⟨α, f⟩ S) /
        (∑ S ∈ U.powersetCard (k + 1), ∏ i ∈ S, w i)

def family : Registration arena.{u} (type_of% (@weighted_slice_rank_comparison.{u})) := by
  have hbad : ¬ arena.Law rejected.{u} := by
    intro h
    let U : Finset (ULift.{u} (Fin 1)) := {⟨0⟩}
    have hc := h U (fun _ => 1) (by simp) (fun _ => 1)
      (by intros; exact le_rfl) 0 (by simp [U])
    norm_num [U, rejected, realize] at hc
  exact {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@weighted_slice_rank_comparison.{u}, rejected, hbad⟩
    sensitivity := by
      constructor
      · intro i
        refine ⟨rejected, ?_, ?_, hbad⟩
        · intro j hj; exact (hj (Subsingleton.elim _ _)).elim
        · funext e; exact nomatch e
      · intro e; exact nomatch e
    dependence := by
      intro i
      let p : signature.Params := ⟨ULift.{u} (Fin 1), fun S => (S.card : ℝ)⟩
      refine ⟨p, ∅, {⟨0⟩}, ?_⟩
      change ((∅ : Finset (ULift.{u} (Fin 1))).card : ℝ) ≠
        (({⟨0⟩} : Finset (ULift.{u} (Fin 1))).card : ℝ)
      simp }

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_slice_rank_comparison.{u})
    (type_of% (realize signature.{u} (fun _ p S => p.2 S) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation.weighted_slice_rank_comparison.__information_unit
  realizationName := `Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p S => p.2 S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev arenaNA : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [DecidableEq α]
    (U : Finset α) (w : α → ℝ) (hw : ∀ i ∈ U, 0 < w i)
    (q : ℕ) (hq : q ≤ U.card)
    (A B : Finset α) (hA : A ⊆ U) (hB : B ⊆ U) (hAB : Disjoint A B)
    (f g : Finset α → ℝ)
    (hf : ∀ S ⊆ A, ∀ T ⊆ A, S ⊆ T → f S ≤ f T)
    (hg : ∀ S ⊆ B, ∀ T ⊆ B, S ⊆ T → g S ≤ g T),
    (∑ S ∈ U.powersetCard q, (∏ i ∈ S, w i) * (f (S ∩ A) * g (S ∩ B))) /
        (∑ S ∈ U.powersetCard q, ∏ i ∈ S, w i) ≤
    ((∑ S ∈ U.powersetCard q, (∏ i ∈ S, w i) * f (S ∩ A)) /
        (∑ S ∈ U.powersetCard q, ∏ i ∈ S, w i)) *
    ((∑ S ∈ U.powersetCard q, (∏ i ∈ S, w i) * R.readout () ⟨α, g⟩ (S ∩ B)) /
        (∑ S ∈ U.powersetCard q, ∏ i ∈ S, w i))

def familyNA : Registration arenaNA.{u} (type_of% (@weighted_slice_negative_association.{u})) := by
  classical
  have hbad : ¬ arenaNA.Law rejected.{u} := by
    intro h
    have hc := h (∅ : Finset (ULift.{u} (Fin 0))) (fun _ => 1) (by simp)
      0 (by simp) ∅ ∅ (by simp) (by simp) (by simp)
      (fun _ => 1) (fun _ => 1) (by intros; rfl) (by intros; rfl)
    norm_num [rejected, realize] at hc
  exact {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@weighted_slice_negative_association.{u}, rejected, hbad⟩
    sensitivity := by
      constructor
      · intro i
        refine ⟨rejected, ?_, ?_, hbad⟩
        · intro j hj; exact (hj (Subsingleton.elim _ _)).elim
        · funext e; exact nomatch e
      · intro e; exact nomatch e
    dependence := by
      intro i
      let p : signature.Params := ⟨ULift.{u} (Fin 1), fun S => (S.card : ℝ)⟩
      refine ⟨p, (∅ : Finset (ULift.{u} (Fin 1))), {⟨0⟩}, ?_⟩
      change ((∅ : Finset (ULift.{u} (Fin 1))).card : ℝ) ≠
        (({⟨0⟩} : Finset (ULift.{u} (Fin 1))).card : ℝ)
      simp }

def registrationNA : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_slice_negative_association.{u})
    (type_of% (realize signature.{u} (fun _ p S => p.2 S) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation.weighted_slice_negative_association.__information_unit
  realizationName := `Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation.familyNA
  realizationSource := none
  generated := false
  arena := .source ⟨arenaNA⟩
  objectArena := .source ⟨arenaNA⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arenaNA ⟨familyNA⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p S => p.2 S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation
    definition := none
    coordinates := #[0, 13]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation
end

open Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation in
#print axioms family

open Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation in
#print axioms familyNA
open Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation in
#print axioms registration
open Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation in
#print axioms registrationNA
