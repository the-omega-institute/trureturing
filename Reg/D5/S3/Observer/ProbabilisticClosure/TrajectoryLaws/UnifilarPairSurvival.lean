import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Matrix Classical
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival
universe u

abbrev Parameters := Σ H : Type u, Σ _δ : H → Bool → H, Σ _n : ℕ, Pair H

@[reducible] def signature : Signature where
  Params := Parameters.{u}
  State t := t.1 → Bool → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ t p => survivingAffinity p t.2.1 t.2.2.1 t.2.2.2) Empty.elim

def rejected : Realization signature :=
  realize signature (fun _ t p => survivingAffinity p t.2.1 t.2.2.1 t.2.2.2 + 1) Empty.elim

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {H : Type u} [Fintype H]
    (p : H → Bool → ℝ) (δ : H → Bool → H)
    (_hp : ∀ a x, 0 ≤ p a x) (n : ℕ) (s : Pair H),
    (∑ t, (pairMatrix p δ ^ n) s t) =
      R.readout () ⟨H, δ, n, s⟩ p

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let s : Pair (ULift.{u} (Fin 2)) := ⟨(⟨0⟩, ⟨1⟩), by decide⟩
  have hcase := @h (ULift.{u} (Fin 2)) inferInstance (fun _ _ => 0) (fun a _ => a)
    (by intro a x; norm_num) 0 s
  have hgood := pair_survival_word_affinity (fun (_ : ULift.{u} (Fin 2)) (_ : Bool) => (0 : ℝ))
    (fun a _ => a) (by intro a x; norm_num) 0 s
  change _ = survivingAffinity (fun _ _ => 0) (fun a _ => a) 0 s + 1 at hcase
  rw [hgood] at hcase
  linarith

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro _
  let s : Pair (ULift.{u} (Fin 2)) := ⟨(⟨0⟩, ⟨1⟩), by decide⟩
  refine ⟨⟨ULift.{u} (Fin 2), (fun a _ => a), 1, s⟩,
    (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  have hne : (⟨0⟩ : ULift.{u} (Fin 2)) ≠ ⟨1⟩ := by decide
  norm_num [actual, realize, survivingAffinity,
    _root_.D5.S3.TotalVariation.Bhattacharyya.bhattacharyya,
    endpoint, wordMass, s, hne]

def family : Registration arena.{u} (type_of% (@pair_survival_word_affinity.{u})) where
  actual := realize signature.{u}
    (fun _ t p => survivingAffinity p t.2.1 t.2.2.1 t.2.2.2) Empty.elim
  bridge := Iff.rfl
  variation := ⟨@pair_survival_word_affinity.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pair_survival_word_affinity.{u})
    (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival.unit
  realizationName :=
    `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ t p => survivingAffinity p t.2.1 t.2.2.1 t.2.2.2) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival
    definition := none
    coordinates := #[0, 3, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival
