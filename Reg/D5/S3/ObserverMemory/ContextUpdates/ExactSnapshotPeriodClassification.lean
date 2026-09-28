import D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification
import Mathlib.Algebra.Group.ULift
import Reg.Support.DependentFamily

open _root_.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification
universe u v w z

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => 2 ^ n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The whole source statement, with only its final power replaced by a readout. -/
def arena : Arena where
  signature := signature
  Law observation := ∀ {G : Type u} {I : Type v} {C : Type w}
    [AddCommGroup G] [Fintype I] {M : I → Type z} [Nontrivial I]
    (P : Protocol G I C M) (χ : G →+ ZMod 2)
    (D : (G × G × ((i : I) → M i)) → G)
    (hD : ∀ s : Source (I := I) χ, D (observe P s) = target s),
    (∀ a t c, Reachable P χ a t c → ∀ i x,
      ∃ s : Source (I := I) χ,
        s.1.1 = a ∧ clock s = t ∧
        P.query s.1.1 (clock s) = c ∧ s.1.2 i = x) ∧
    (∀ i, senderPeriods P χ i = ⊥ ∨ ∃ τ : G,
      τ ≠ 0 ∧ χ τ = 1 ∧ τ + τ = 0 ∧
      ∀ p, p ∈ senderPeriods P χ i ↔ p = 0 ∨ p = τ) ∧
    (∀ i j p q, p ∈ senderPeriods P χ i → q ∈ senderPeriods P χ j →
      p ≠ 0 → q ≠ 0 → p = q) ∧
    (∀ v : Source (I := I) χ, v ∈ globalPeriods P χ ↔
      v.1.1 = 0 ∧ v.2 = 0 ∧ (∀ i, v.1.2 i ∈ senderPeriods P χ i) ∧
        ∑ i, v.1.2 i = 0) ∧
    ( (activeSenders P χ).card ≤ 1 → globalPeriods P χ = ⊥) ∧
    ( (activeSenders P χ).Nonempty →
      Nonempty (globalPeriods P χ ≃+ evenSwitches (activeSenders P χ)) ∧
      Nat.card (globalPeriods P χ) = observation.readout () () ((activeSenders P χ).card - 1))

theorem actual_law : arena.{u, v, w, z}.Law actual := by
  intro G I C _ _ M _ P χ D hD
  exact period_classification P χ D hD

/-- Constant replies with an injective clock give a genuine nonempty active family. -/
theorem rejected_law : ¬ arena.{u, v, w, z}.Law rejected := by
  classical
  intro h
  let G := ULift.{u} (ZMod 2)
  let I := ULift.{v} Bool
  let C := ULift.{w} Unit
  let M : I → Type z := fun _ => ULift.{z} Unit
  let P : Protocol G I C M := {
    query := fun _ _ => ⟨()⟩
    reply := fun _ _ _ _ => ⟨()⟩ }
  let χ : G →+ ZMod 2 := AddEquiv.ulift.toAddMonoidHom
  let D : (G × G × ((i : I) → M i)) → G := fun q => q.2.1
  have hD : ∀ s : Source (I := I) χ, D (observe P s) = target s := by
    intro s
    change target s + (s.2 : G) = target s
    have hz : (s.2 : G) = 0 := by
      apply ULift.ext
      exact s.2.property
    rw [hz, add_zero]
  have hactive : (activeSenders P χ).Nonempty := by
    refine ⟨⟨false⟩, ?_⟩
    simp only [activeSenders, Finset.mem_filter, Finset.mem_univ, true_and]
    intro heq
    have hp : (⟨1⟩ : G) ∈ senderPeriods P χ ⟨false⟩ := by
      intro a t c hb x
      rfl
    rw [heq] at hp
    have hz := congrArg ULift.down (AddSubgroup.mem_bot.mp hp)
    exact one_ne_zero hz
  have hbad := ((h P χ D hD).2.2.2.2.2 hactive).2
  change Nat.card (globalPeriods P χ) = 0 at hbad
  exact (Nat.ne_of_gt (Nat.card_pos (α := globalPeriods P χ))) hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (1 : ℕ) ≠ 2
  decide

def registration : Registration arena.{u, v, w, z} (arena.Law actual) :=
  Registration.mk actual Iff.rfl
    ⟨actual_law, rejected, rejected_law⟩
    (by
      constructor
      · intro i
        refine ⟨rejected, ?_, rfl, rejected_law⟩
        intro j h
        exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
      · intro i
        exact nomatch i)
    dependence

register_information_theorem
  _root_.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.period_classification
  in arena
  readout via (realize signature (fun _ _ n => 2 ^ n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "arg", "arg", "arg", "arg", "body", "arg", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification
