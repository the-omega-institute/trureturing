/- GID: D5/S3/Observer/Existence/ExistenceLayersDoNotImply
   generality: G
   mirror-B: D5/B/S3/Observer/Existence/ExistenceLayersDoNotImply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three Boolean models separate type, interface, causal, and record existence. -/

import Mathlib.Logic.Function.Iterate

/- Library-search audit trail (2026-08-22):
   * Exact searches for all three main theorem names in `D5` and
     `Golden/Frozen/accepted` found no matches.
   * Repository searches for existence, distinguishability, causality, and records found
     future-readout and distinguishing-time infrastructure, but no public theorem giving any
     of these three countermodels. Private hits were unrelated iteration auxiliaries.
   * Pinned Mathlib provides `Function.iterate_succ_apply` and the basic iteration machinery;
     no theorem packages these model-specific non-implications, so the proofs use finite
     `Bool` and `Unit` witnesses with simplification of constant and identity functions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Existence.ExistenceLayersDoNotImply

/-- A particular distinction exists at the type level when its states are unequal. -/
def TypeExistence {X : Type*} (x y : X) : Prop :=
  x ≠ y

/-- A particular distinction exists operationally when the interface separates its states. -/
def DistinguishableExistence {X O : Type*} (q : X -> O) (x y : X) : Prop :=
  q x ≠ q y

/-- A particular distinction has causal existence when some positive-time readout separates it. -/
def CausalExistence {X O : Type*} (T : X -> X) (q : X -> O) (x y : X) : Prop :=
  ∃ k : Nat, q ((T^[k + 1]) x) ≠ q ((T^[k + 1]) y)

/-- A distinction has record existence when a stable record center separates its states. -/
def RecordExistence {X R : Type*} (T : X -> X) (record : X -> R)
    (x y : X) : Prop :=
  record x ≠ record y ∧ ∀ z, record (T z) = record z

/-- Distinct Boolean states remain type-level distinctions even through a constant interface. -/
theorem type_existence_does_not_imply_distinguishable_existence :
    ∃ (X O : Type) (x y : X) (q : X -> O),
      TypeExistence x y ∧ ¬DistinguishableExistence q x y := by
  refine ⟨Bool, Unit, false, true, fun _ => (), ?_, ?_⟩
  · simp [TypeExistence]
  · simp [DistinguishableExistence]

/-- An identity interface distinguishes two states now, although a constant update merges every
positive-time future. -/
theorem distinguishable_existence_does_not_imply_causal_existence :
    ∃ (X O : Type) (T : X -> X) (q : X -> O) (x y : X),
      DistinguishableExistence q x y ∧ ¬CausalExistence T q x y := by
  refine ⟨Bool, Bool, fun _ => false, id, false, true, ?_, ?_⟩
  · simp [DistinguishableExistence]
  · simp [CausalExistence, Function.iterate_succ_apply]

/-- Identity dynamics preserve a causal distinction that a constant stable center never records. -/
theorem causal_existence_does_not_imply_record_existence :
    ∃ (X O R : Type) (T : X -> X) (q : X -> O) (record : X -> R) (x y : X),
      CausalExistence T q x y ∧
        (∀ z, record (T z) = record z) ∧
        ¬RecordExistence T record x y := by
  refine ⟨Bool, Bool, Unit, id, id, fun _ => (), false, true, ?_, ?_, ?_⟩
  · refine ⟨0, ?_⟩
    decide
  · intro z
    rfl
  · simp [RecordExistence]

example : TypeExistence false true := by
  simp [TypeExistence]

#print axioms type_existence_does_not_imply_distinguishable_existence
#print axioms distinguishable_existence_does_not_imply_causal_existence
#print axioms causal_existence_does_not_imply_record_existence

end D5.S3.Observer.Existence.ExistenceLayersDoNotImply
