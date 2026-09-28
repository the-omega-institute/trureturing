import D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity
import Reg.Support.DependentFamily

open _root_.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity
open _root_.D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity

universe u v z

@[reducible] def signature : Signature where
  Params := Σ S : Type u, Σ A : Type v, Σ _ : S → S, Σ _ : S → A, ℕ
  State p := WindowState p.2.2.1 p.2.2.2.1 p.2.2.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ w => firstLetter w) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ p w => w.1 ⟨p.2.2.2.2, by omega⟩) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {S : Type u} {A : Type v} [Finite S] (D : S → S) (q : S → A) (n : ℕ),
    (∀ (M : Type z) [Finite M] (I : S → M) (F : M → M) (g : M → A),
      WindowCorrect D q n I F g → Nat.card (WindowState D q n) ≤ Nat.card M) ∧
    (Finite (WindowState D q n) ∧ Function.Surjective (prepare D q n)) ∧
    (∃ r : WindowState D q n → S, Function.RightInverse r (prepare D q n)) ∧
    ∀ r : WindowState D q n → S, Function.RightInverse r (prepare D q n) →
      WindowCorrect D q n (prepare D q n) (representativeUpdate D q n r)
          (R.readout () ⟨S, A, D, q, n⟩) ∧
      ∀ (w : WindowState D q n) (t : ℕ),
        futureReadoutWord (representativeUpdate D q n r) firstLetter n
            ((representativeUpdate D q n r)^[t] w) =
          ((representativeUpdate D q n r)^[t] w).1

theorem actual_law : arena.{u,v,z}.Law actual := by
  exact free_window_realization_capacity

theorem rejected_law : ¬ arena.{u,v,z}.Law rejected := by
  intro h
  let D : ULift.{u} Bool → ULift.{u} Bool := fun s => ⟨!s.down⟩
  let q : ULift.{u} Bool → ULift.{v} Bool := fun s => ⟨s.down⟩
  have hs := h D q 1
  obtain ⟨r, hr⟩ := hs.2.2.1
  have hx := (hs.2.2.2 r hr).1 (ULift.up false) (0 : Fin 2)
  have impossible : (true : Bool) = false := congrArg ULift.down hx
  exact Bool.noConfusion impossible

def registration : Registration arena.{u,v,z} (arena.{u,v,z}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    let D : ULift.{u} Bool → ULift.{u} Bool := id
    let q : ULift.{u} Bool → ULift.{v} Bool := fun s => ⟨s.down⟩
    refine ⟨⟨ULift.{u} Bool, ULift.{v} Bool, D, q, 0⟩,
      prepare D q 0 (ULift.up false), prepare D q 0 (ULift.up true), ?_⟩
    intro h
    exact Bool.noConfusion (congrArg ULift.down h)

register_information_theorem free_window_realization_capacity in arena
  readout via (realize signature.{u,v}
    (fun _ p w => @firstLetter p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 w)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity
    coordinates := #[0, 1, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg",
        "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity
