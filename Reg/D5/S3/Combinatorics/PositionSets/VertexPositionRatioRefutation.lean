import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation
import Reg.Support.UniverseSingleReadout

/-! Source-bound audit of graph distance in the potential estimate. -/

namespace Reg.D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation

open _root_.D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev Params := Σ V : Type, Σ _ : SimpleGraph V, V

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Params
    (fun p => Sigma.fst p) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature
    (fun _ p v => (Sigma.fst (Sigma.snd p)).dist (Sigma.snd (Sigma.snd p)) v)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type} (G : SimpleGraph V) (f : V → ℕ)
    (_hf : ∀ u v, G.Adj u v → f u ≤ f v + 1)
    {u v : V} (_hr : G.Reachable u v),
    f u ≤ f v + R.readout () ⟨V, G, u⟩ v

theorem actual_law : arena.Law actual := by
  intro V G f hf u v hr
  exact potential_dist G f hf hr

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let f : Bool → ℕ := fun b => if b then 0 else 1
  have hf : ∀ a b, (⊤ : SimpleGraph Bool).Adj a b → f a ≤ f b + 1 := by
    intro a b _
    cases a <;> cases b <;> simp [f]
  have hr : (⊤ : SimpleGraph Bool).Reachable false true := by simp
  have hb := h (V := Bool) (⊤ : SimpleGraph Bool) f hf (u := false) (v := true) hr
  change 1 ≤ 0 + 0 at hb
  omega

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Bool, ⊤, false⟩, false, true, ?_⟩
  change (⊤ : SimpleGraph Bool).dist false false ≠
    (⊤ : SimpleGraph Bool).dist false true
  rw [SimpleGraph.dist_self]
  have hdist : (⊤ : SimpleGraph Bool).dist false true = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr
      ((SimpleGraph.top_adj false true).2 (by decide))
  rw [hdist]
  exact Nat.zero_ne_one

def source_registration : Registration arena (type_of% @potential_dist) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@potential_dist) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p v => (Sigma.fst (Sigma.snd p)).dist (Sigma.snd (Sigma.snd p)) v)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation
