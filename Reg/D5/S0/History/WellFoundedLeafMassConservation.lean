import D5.S0.History.WellFoundedLeafMassConservation
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.History.WellFoundedLeafMassConservation
namespace Reg.D5.S0.History.WellFoundedLeafMassConservation
universe u
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Σ E : Type u, Σ _T : Set (List E), List E → ENNReal
  State := fun p => List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ENNReal
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p h => p.2.2 h) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [Countable E] (T : Set (List E))
    (_root : [] ∈ T)
    (_prefixclosed : ∀ ⦃h k : List E⦄, h.IsPrefix k → k ∈ T → h ∈ T)
    (m : List E → ENNReal)
    (_wf : WellFounded (fun k h : List E =>
      k ∈ T ∧ h ∈ T ∧ ∃ a : E, k = h ++ [a]))
    (_localMass : ∀ h ∈ T, ¬ (h ∈ T ∧ ∀ a : E, h ++ [a] ∉ T) →
      m h = ∑' a : E, if h ++ [a] ∈ T then m (h ++ [a]) else 0),
    (∑' l : {h : List E // h ∈ T ∧ ∀ a : E, h ++ [a] ∉ T}, m l.val) =
      R.readout () ⟨E, T, m⟩ []

def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

def sample : List (ULift.{u} Unit) → ENNReal := fun h => if h = [] then 1 else 0

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let T : Set (List (ULift.{u} Unit)) := {[]}
  have root : [] ∈ T := by simp [T]
  have pc : ∀ ⦃h k : List (ULift.{u} Unit)⦄, h.IsPrefix k → k ∈ T → h ∈ T := by
    intro h k hp hk
    have hk' : k = [] := hk
    subst k
    simpa [T] using hp
  have wf : WellFounded (fun k h : List (ULift.{u} Unit) =>
      k ∈ T ∧ h ∈ T ∧ ∃ a, k = h ++ [a]) := by
    constructor
    intro h
    constructor
    intro k hk
    rcases hk with ⟨hk, _, a, ha⟩
    have hk' : k = [] := hk
    subst k
    simp at ha
  have terminal : ∀ h ∈ T, h ∈ T ∧ ∀ a : ULift.{u} Unit, h ++ [a] ∉ T := by
    intro h ht
    exact ⟨ht, by intro a; simp [T]⟩
  have bad := h T root pc sample wf (by
    intro h ht hn
    exact (hn (terminal h ht)).elim)
  have good := result T root pc sample wf (by
    intro h ht hn
    exact (hn (terminal h ht)).elim)
  rw [good] at bad
  simpa [sample, rejected, realize] using bad

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨⟨ULift.{u} Unit, {[]}, sample⟩, [], [⟨()⟩], by
      simp [actual, realize, sample]⟩

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S0.History.WellFoundedLeafMassConservation
  coordinates := #[0, 2, 5]
  readouts := #[{path := #["body", "body", "body", "body", "body", "body",
    "body", "body", "arg"], stateOperand := some #["arg"]}] }

register_information_theorem result in arena
  readout via (realize signature.{u} (fun _ p h => p.2.2 h) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

#print axioms registration
end
end Reg.D5.S0.History.WellFoundedLeafMassConservation
