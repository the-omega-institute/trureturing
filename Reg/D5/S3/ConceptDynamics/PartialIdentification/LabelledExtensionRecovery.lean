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


namespace InfiniteAudit

/-- The complete source parameters; countability and past finiteness remain law premises. -/
structure Params where
  E : Type u
  order : PartialOrder E
  A : Type v
  label : E → A

attribute [instance] Params.order

abbrev signature : Signature where
  Params := Params.{u, v}
  State p := History p.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ → p.A
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} := realize signature
  (fun _ p h n => p.label (h.val n)) (fun e => nomatch e)

/-- Retaining only the first event's label erases later history information. -/
def rejected : Realization signature.{u, v} := realize signature
  (fun _ p h _ => p.label (h.val 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law obs := ∀ {E : Type u} [order : PartialOrder E] {A : Type v}
    [Countable E] [Infinite E] (_ : ∀ x : E, (Set.Iio x).Finite) (label : E → A),
    Nonempty (History E) ∧
      ((∀ a b : E, label a = label b → a ≤ b ∨ b ≤ a) ↔
        Function.Injective (obs.readout () ⟨E, order, A, label⟩))

def bridge : (type_of% (@infinite_result.{u, v})) ↔ arena.{u, v}.Law actual := Iff.rfl

private def testParams : Params.{u, v} where
  E := ULift.{u} ℕ
  order := discreteOrder _
  A := ULift.{v} ℕ
  label x := ⟨x.down⟩

private def testHistory (σ : ℕ ≃ ℕ) :
    @History testParams.{u, v}.E testParams.order := by
  let e : ℕ ≃ testParams.{u, v}.E := σ.trans Equiv.ulift.symm
  refine ⟨e, ?_⟩
  intro i j hij hji
  change e j = e i at hji
  exact (ne_of_gt hij) (e.injective hji)

private theorem test_past (x : testParams.{u, v}.E) :
    (@Set.Iio _ testParams.order.toPreorder x).Finite := by
  apply Set.finite_empty.subset
  intro y hy
  change y = x ∧ ¬ x = y at hy
  exact (hy.2 hy.1.symm).elim

private theorem test_chains :
    ∀ a b : testParams.{u, v}.E,
      testParams.label a = testParams.label b →
        @LE.le _ testParams.order.toLE a b ∨ @LE.le _ testParams.order.toLE b a := by
  intro a b h
  left
  change a = b
  exact congrArg (fun z : ULift.{v} ℕ => (ULift.up z.down : ULift.{u} ℕ)) h

private theorem rejected_fails : ¬ arena.{u, v}.Law rejected := by
  intro h
  have hi := (@h testParams.E testParams.order testParams.A
    (show Countable (ULift.{u} ℕ) from inferInstance)
    (show Infinite (ULift.{u} ℕ) from inferInstance)
    test_past testParams.label).2.mp test_chains
  have heq := hi (a₁ := testHistory (Equiv.refl ℕ))
    (a₂ := testHistory (Equiv.swap 1 2)) (by
      funext n
      simp [rejected, realize, testHistory, testParams, Equiv.swap_apply_def])
  have h12 := congrArg (fun h : @History testParams.{u, v}.E testParams.order =>
    (h.val 1).down) heq
  change (1 : ℕ) = 2 at h12
  exact (by decide : (1 : ℕ) ≠ 2) h12

private theorem actual_dependence : ObservationalDependence signature actual.{u, v} := by
  intro i
  refine ⟨testParams, testHistory (Equiv.refl ℕ), testHistory (Equiv.swap 0 1), ?_⟩
  intro h
  have h01 := congrArg ULift.down (congrFun h 0)
  change (0 : ℕ) = 1 at h01
  exact Nat.noConfusion h01

def family : Registration arena.{u, v} (type_of% (@infinite_result.{u, v})) where
  actual := realize signature actual.readout actual.anchor
  bridge := bridge
  variation := ⟨bridge.mp (@infinite_result.{u, v}), rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

#print axioms family

end InfiniteAudit


#print axioms family

end Reg.D5.S3.ConceptDynamics.PartialIdentification.LabelledExtensionRecovery
