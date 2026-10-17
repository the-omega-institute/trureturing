import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Shadowing.CoherentFollowerCover
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Shadowing.CoherentFollower
open _root_.D5.S1.Dynamics.Shadowing.CoherentFollower.LanguageSystem

namespace Reg.D5.S1.Dynamics.Shadowing.CoherentFollowerCover

noncomputable section
universe u v

abbrev boundSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def boundActual : Realization boundSignature :=
  realize boundSignature (fun _ m k => decide (m ≤ k)) (fun e => nomatch e)

def boundRejected : Realization boundSignature :=
  realize boundSignature (fun _ _ _ => false) (fun e => nomatch e)

/-- Reify precisely the cardinal comparison, retaining the entire telescope. -/
abbrev boundArena : Arena where
  signature := boundSignature
  Law R := ∀ {I : Type u} {A : I → Type v} [∀ i, TopologicalSpace (A i)]
    (S : LanguageSystem A) [∀ i, Finite (A i)] (F : Finset I),
    letI := Fintype.ofFinite (Face F)
    R.readout () (Nat.card (S.Vertex F)) (Nat.card (Letter A F) *
      ∏ H : Face F, Nat.card (Followers (S.language H.1))) = true

private theorem boundActual_law : boundArena.{u,v}.Law boundActual := by
  simpa only [boundArena, boundActual, realize, decide_eq_true_eq] using
    (@vertex_card_bound_product.{u,v})

private abbrev unitAlphabet (_ : ULift.{u} Unit) := ULift.{v} Unit

private def unitSystem : @LanguageSystem (ULift.{u} Unit) unitAlphabet
    (fun _ => inferInstance) where
  language _ := Set.univ
  nonempty _ := ⟨fun _ _ => ⟨()⟩, trivial⟩
  closed _ := isClosed_univ
  forward _ _ _ := trivial
  finite_followers _ := by
    apply Finite.of_injective (fun _ : Followers (Set.univ : Set (ScopedWord unitAlphabet _)) => ())
    intro q r _
    apply Subtype.ext
    obtain ⟨u, hu, _⟩ := q.2
    obtain ⟨v, hv, _⟩ := r.2
    rw [hu, hv]
    rfl
  image_eq h := by
    ext z
    constructor
    · intro _; trivial
    · intro _
      refine ⟨fun _ _ => ⟨()⟩, trivial, ?_⟩
      funext n i
      exact Subsingleton.elim _ _

private theorem boundRejected_law : ¬ boundArena.{u,v}.Law boundRejected := by
  intro h
  have hb := @h (ULift.{u} Unit) unitAlphabet (fun _ => inferInstance) unitSystem
    (fun _ => inferInstance) ∅
  change false = true at hb
  contradiction

def boundRegistration : Registration boundArena.{u,v}
    (type_of% (@vertex_card_bound_product.{u,v})) where
  actual := boundActual
  bridge := by simp only [boundActual, realize, decide_eq_true_eq]
  variation := ⟨boundActual_law, boundRejected, boundRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨boundRejected, ?_, rfl, boundRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    exact ⟨1, 0, 1, by change (false : Bool) ≠ true; decide⟩

noncomputable def registration_bound : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@vertex_card_bound_product.{u,v}) (Realization boundSignature) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.CoherentFollowerCover.cardinalBound
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.CoherentFollowerCover.boundRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨boundArena.{u,v}⟩
  objectArena := .source ⟨boundArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundArena.{u,v} ⟨boundRegistration.{u,v}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize boundSignature (fun _ m k => decide (m ≤ k))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.CoherentFollowerCover
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms boundRegistration

end
end Reg.D5.S1.Dynamics.Shadowing.CoherentFollowerCover
