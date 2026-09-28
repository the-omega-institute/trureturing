import D5.S3.ObserverMemory.Realization.CommutingReversibleRealization
import Reg.Support.DependentFamily

open _root_.D5.S3.ObserverMemory.Realization.CommutingReversibleRealization
open _root_.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity
open _root_.D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open _root_.D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ObserverMemory.Realization.CommutingReversibleRealization

universe u

@[reducible] def signature : Signature where
  Params := Σ S : Type u, Σ A : Type u, Σ _ : S → S, Σ _ : S → A, ℕ
  State p := ItineraryRange p.2.2.1 p.2.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ t => t.1 0) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ t => t.1 1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R :=
    ∀ {S A : Type u} [Finite S] [Nonempty S] [Finite A]
    (D : S → S) (q : S → A) (n : ℕ),
    let T := ItineraryRange D q
    let ι : S → T := Set.rangeFactorization (completeItinerary D q)
    let σ := itineraryUpdate D q
    let gT : T → A := R.readout () ⟨S, A, D, q, n⟩
    (∀ (M : Type u) [Finite M] (I : S → M) (F : M → M) (g : M → A),
      (∀ s, I (D s) = F (I s)) → WindowCorrect D q n I F g →
      (∀ s j, g (F^[j] (I s)) = q (D^[j] s)) ∧
      Nat.card T ≤ Nat.card (Set.range I) ∧
      Nat.card (Set.range I) ≤ Nat.card M ∧
      (Function.Bijective F → Function.Bijective σ)) ∧
    (Finite T ∧ Function.Surjective ι ∧
      (∀ s, ι (D s) = σ (ι s)) ∧ WindowCorrect D q n ι σ gT) ∧
    ((∃ (M : Type u) (_ : Finite M) (I : S → M) (F : M → M) (g : M → A),
        (∀ s, I (D s) = F (I s)) ∧ WindowCorrect D q n I F g ∧
        Function.Bijective F) ↔ Function.Injective σ) ∧
    (Function.Injective σ ↔ Function.Bijective σ) ∧
    (Nat.card T = Nat.card (FiniteItineraryRange D q n) ↔
      Setoid.ker (futureReadoutWord D q n) =
        Setoid.ker (futureReadoutWord D q (n + 1)))

theorem actual_law : arena.{u}.Law actual := by
  exact commuting_reversible_realization

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let D : ULift.{u} Bool → ULift.{u} Bool := fun s => ⟨!s.down⟩
  let q : ULift.{u} Bool → ULift.{u} Bool := id
  have hs := h D q 0
  have hx := hs.2.1.2.2.2 (ULift.up false) (0 : Fin 1)
  have impossible : (true : Bool) = false := congrArg ULift.down hx
  exact Bool.noConfusion impossible

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    let D : ULift.{u} Bool → ULift.{u} Bool := id
    let q : ULift.{u} Bool → ULift.{u} Bool := id
    refine ⟨⟨ULift.{u} Bool, ULift.{u} Bool, D, q, 0⟩,
      Set.rangeFactorization (completeItinerary D q) (ULift.up false),
      Set.rangeFactorization (completeItinerary D q) (ULift.up true), ?_⟩
    intro h
    exact Bool.noConfusion (congrArg ULift.down h)

register_information_theorem commuting_reversible_realization in arena
  readout via (realize signature.{u} (fun _ _ t => t.1 0) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ObserverMemory.Realization.CommutingReversibleRealization
    coordinates := #[0, 1, 5, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.ObserverMemory.Realization.CommutingReversibleRealization
