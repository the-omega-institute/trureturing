import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.FourVertexPortPulses
import Reg.Support.DependentFamily

open LeanInformationAudit Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.Linear.FourVertexPortPulses

noncomputable section

namespace Reg.D5.S3.Observer.Linear.FourVertexPortPulses

abbrev signature : Signature where
  Params := Unit
  State _ := Finset ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ S => S.card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def theoremLaw (F : Realization signature) : Prop :=
  ∀ (M γ q : ℝ) (_hM : 0 < M) (_hγ : 0 < γ)
    (_hcap : γ ≤ M / 256) (_hq : 0 < q) (_hqle : q ≤ γ ^ 2 / M),
    (∀ r, (laplacian M γ q r).PosSemidef ∧ (∀ i, ∑ j, laplacian M γ q r i j = 0) ∧
      ∀ i j, i ≠ j → 0 < -laplacian M γ q r i j) ∧
    (∀ r S w, endpoint (laplacian M γ q r) S w = target →
      4 ≤ F.readout () () S ∧ ∑ t ∈ S, w t = 0) ∧
    (∀ S : Finset ℝ, S.card = 4 → ∃ w : ℝ → ℝ, (∑ t ∈ S, w t) = 0 ∧
      ∀ r, endpoint (laplacian M γ q r) S w = target) ∧
    ∀ T : ℝ, 0 < T → ∃ (S : Finset ℝ) (w : ℝ → ℝ),
      S.card = 4 ∧ (∀ t ∈ S, 0 < t ∧ t ≤ T) ∧ (∑ t ∈ S, w t) = 0 ∧
      ∀ r, endpoint (laplacian M γ q r) S w = target

def arena : Arena where
  signature := signature
  Law := theoremLaw

private theorem rejected_law : ¬ arena.Law rejected := by
  intro H
  have bad := H 256 1 (1 / 256) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨S, w, _, _, _, hep⟩ := bad.2.2.2 1 (by norm_num)
  have hc := (bad.2.1 false S w (hep false)).1
  norm_num [rejected, realize] at hc

def family : Registration arena (type_of% @exact_four_ages) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_four_ages, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro role
    refine ⟨(), ∅, {0}, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exact_four_ages)
    (type_of% (realize signature (fun _ _ S => S.card) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.FourVertexPortPulses.exact_four_ages.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.FourVertexPortPulses.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => S.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.FourVertexPortPulses
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Observer.Linear.FourVertexPortPulses
