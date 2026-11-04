import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Codes.KhesinLiBipartiteEncoderEquivalence
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations of the selected public mathematical statements. -/

namespace Reg.D5.S3.Quantum.Codes.KhesinLiBipartiteEncoderEquivalence
open _root_.D5.S3.Quantum.Codes.KhesinLiBipartiteEncoderEquivalence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open _root_.D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses (Step)

/-- Observe the full reachability relation at each encoder size. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ)
    (fun p => SimpleGraph (Fin p.1 ⊕ Fin p.2))
    (fun p => SimpleGraph (Fin p.1 ⊕ Fin p.2) → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ G H => Relation.ReflTransGen BipartiteStep G H)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ k n : ℕ, ∀ G H : SimpleGraph (Fin k ⊕ Fin n),
    G.IsBipartiteWith {v | v.isLeft} {v | v.isRight} →
      H.IsBipartiteWith {v | v.isLeft} {v | v.isRight} → Relation.EqvGen Step G H →
      R.readout () ⟨k, n⟩ G H

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let G : SimpleGraph (Fin 0 ⊕ Fin 0) := ⊥
  have hb : G.IsBipartiteWith {v | v.isLeft} {v | v.isRight} := by
    constructor
    · exact Set.disjoint_left.mpr (fun v => Fin.elim0 (Sum.elim id id v))
    · intro a b hab
      exact hab.elim
  exact h 0 0 G G hb hb (.refl G)

private theorem reachable_bot {H : SimpleGraph (Fin 0 ⊕ Fin 2)}
    (h : Relation.ReflTransGen BipartiteStep ⊥ H) : H = ⊥ := by
  induction h with
  | refl => rfl
  | @tail H J h step ih =>
      rcases step with ⟨σ, hσ⟩ | ⟨τ, hτ⟩ | ⟨i, j, _, _⟩
      · rw [hσ, ih]
        ext a b
        simp [SimpleGraph.map_adj']
      · rw [hτ, ih]
        ext a b
        simp [SimpleGraph.map_adj']
      · exact Fin.elim0 i

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 2⟩, ⊥, ⊤, ?_⟩
  intro h
  have he : Relation.ReflTransGen BipartiteStep
      (⊥ : SimpleGraph (Fin 0 ⊕ Fin 2)) ⊤ :=
    Eq.mpr (congrFun h ⊤) .refl
  have hbot := reachable_bot he
  have edge : (⊤ : SimpleGraph (Fin 0 ⊕ Fin 2)).Adj (Sum.inr 0) (Sum.inr 1) := by simp
  rw [hbot] at edge
  exact edge

def source_registration : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Codes.KhesinLiBipartiteEncoderEquivalence.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Codes.KhesinLiBipartiteEncoderEquivalence "source_registration"
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
    owner := `D5.S3.Quantum.Codes.KhesinLiBipartiteEncoderEquivalence
    definition := some {
      owner := `D5.S3.Quantum.Codes.KhesinLiBipartiteEncoderEquivalence
      name := `D5.S3.Quantum.Codes.KhesinLiBipartiteEncoderEquivalence.claim
      path := #[] }
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Codes.KhesinLiBipartiteEncoderEquivalence
