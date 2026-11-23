import D5.S3.ConceptDynamics.PartialIdentification.LabelledExtensionRecovery
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.ConceptDynamics.PartialIdentification.LabelledExtensionRecovery

open _root_.D5.S3.ConceptDynamics.PartialIdentification.LabelledExtensionRecovery
open _root_.D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u v

structure Params where
  E : Type u
  order : PartialOrder E
  A : Type v
  F : Finset E
  label : E → A

attribute [instance] Params.order

abbrev signature : Signature where
  Params := Params.{u, v}
  State p := List p.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List p.A
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} := realize signature
  (fun _ p l => l.map p.label) (fun e => nomatch e)

def rejected : Realization signature.{u, v} := realize signature
  (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law obs := ∀ p : Params.{u, v},
    (∀ a ∈ p.F, ∀ b ∈ p.F, p.label a = p.label b → a ≤ b ∨ b ≤ a) ↔
    ∀ l m : List p.E,
      ExtensionList (∅ : Set p.E) (p.F : Set p.E) l →
      ExtensionList (∅ : Set p.E) (p.F : Set p.E) m →
      obs.readout () p l = obs.readout () p m → l = m

def bridge : (type_of% (@_root_.D5.S3.ConceptDynamics.PartialIdentification.LabelledExtensionRecovery.result.{u, v})) ↔ arena.{u, v}.Law actual := by
  constructor
  · intro h p
    exact @h p.E p.order p.A p.F p.label
  · intro h E order A F label
    exact h ⟨E, order, A, F, label⟩

private def discreteOrder (T : Type u) : PartialOrder T where
  le := Eq
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h

private def witness : Params.{u, v} where
  E := ULift.{u} Nat
  order := discreteOrder _
  A := ULift.{v} Nat
  F := {⟨0⟩, ⟨1⟩}
  label x := ⟨x.down⟩

/-- Completing the audit requires a rejected observation family. -/
def family (negative : ¬ arena.{u, v}.Law rejected) : Registration arena.{u, v} (type_of% (@_root_.D5.S3.ConceptDynamics.PartialIdentification.LabelledExtensionRecovery.result.{u, v})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@_root_.D5.S3.ConceptDynamics.PartialIdentification.LabelledExtensionRecovery.result.{u, v}), rejected, negative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, negative⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨witness, [], [⟨0⟩], ?_⟩
    simp [actual, realize]


#print axioms family

end Reg.D5.S3.ConceptDynamics.PartialIdentification.LabelledExtensionRecovery
