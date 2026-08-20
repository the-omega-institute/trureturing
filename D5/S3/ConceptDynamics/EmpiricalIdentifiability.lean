/- GID: D5/S3/ConceptDynamics/EmpiricalIdentifiability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/EmpiricalIdentifiability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Protocol outcomes determine exactly which model properties descend uniquely. -/

import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-21):
   * Pinned Mathlib provides the exact quotient constructors `Quotient.lift`,
     `Quotient.lift_mk`, and `Quotient.sound`; all are applied below.
   * `Function.factorsThrough_iff` is an adjacent fiber-factorization criterion,
     but it neither constructs the source's empirical setoid nor states uniqueness.
   * Repository searches for empirical identifiability and protocol-outcome
     quotients found no declaration packaging both public source clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.EmpiricalIdentifiability

/-- Two models are empirically equivalent when every allowed protocol has the
same outcome on them. -/
def empiricalSetoid {Protocol Theory : Type*} {Outcome : Protocol → Type*}
    (outcome : ∀ protocol, Theory → Outcome protocol) : Setoid Theory where
  r theory theory' := ∀ protocol, outcome protocol theory = outcome protocol theory'
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h protocol => (h protocol).symm
    trans := fun h h' protocol => (h protocol).trans (h' protocol) }

/-- The empirical model space constructed from all allowed protocol outcomes. -/
abbrev EmpiricalQuotient {Protocol Theory : Type*} {Outcome : Protocol → Type*}
    (outcome : ∀ protocol, Theory → Outcome protocol) :=
  Quotient (empiricalSetoid outcome)

/-- The canonical empirical class of a model. -/
def empiricalClass {Protocol Theory : Type*} {Outcome : Protocol → Type*}
    (outcome : ∀ protocol, Theory → Outcome protocol) (theory : Theory) :
    EmpiricalQuotient outcome :=
  Quotient.mk (empiricalSetoid outcome) theory

/-- A model property is identifiable exactly when it is constant on every
protocol-outcome fiber, in which case it descends uniquely to the empirical
quotient. An empirically equivalent pair with different property values blocks
every such descent. -/
theorem empirical_identifiability
    {Protocol Theory Target : Type*} {Outcome : Protocol → Type*}
    (outcome : ∀ protocol, Theory → Outcome protocol)
    (property : Theory → Target) :
    ((∃! descend : EmpiricalQuotient outcome → Target,
        property = descend ∘ empiricalClass outcome) ↔
      ∀ ⦃theory theory' : Theory⦄,
        (∀ protocol, outcome protocol theory = outcome protocol theory') →
          property theory = property theory') ∧
      ((∃ theory theory' : Theory,
          (∀ protocol, outcome protocol theory = outcome protocol theory') ∧
            property theory ≠ property theory') →
        ¬∃ descend : EmpiricalQuotient outcome → Target,
          property = descend ∘ empiricalClass outcome) := by
  constructor
  · constructor
    · rintro ⟨descend, hdescend, _⟩ theory theory' hsame
      calc
        property theory = descend (empiricalClass outcome theory) := by
          simpa only [Function.comp_apply] using congrFun hdescend theory
        _ = descend (empiricalClass outcome theory') :=
          congrArg descend (Quotient.sound hsame)
        _ = property theory' := by
          simpa only [Function.comp_apply] using (congrFun hdescend theory').symm
    · intro hfiber
      let descend : EmpiricalQuotient outcome → Target :=
        Quotient.lift property (by
          intro theory theory' hsame
          exact hfiber hsame)
      refine ⟨descend, ?_, ?_⟩
      · funext theory
        simp only [Function.comp_apply, empiricalClass, descend, Quotient.lift_mk]
      · intro other hother
        funext empiricalTheory
        refine Quotient.inductionOn empiricalTheory (fun theory => ?_)
        calc
          other (empiricalClass outcome theory) = property theory := by
            simpa only [Function.comp_apply] using (congrFun hother theory).symm
          _ = descend (empiricalClass outcome theory) := by
            simp only [empiricalClass, descend, Quotient.lift_mk]
  · rintro ⟨theory, theory', hsame, hdifferent⟩ ⟨descend, hdescend⟩
    apply hdifferent
    calc
      property theory = descend (empiricalClass outcome theory) := by
        simpa only [Function.comp_apply] using congrFun hdescend theory
      _ = descend (empiricalClass outcome theory') :=
        congrArg descend (Quotient.sound hsame)
      _ = property theory' := by
        simpa only [Function.comp_apply] using (congrFun hdescend theory').symm

/-- Constant protocol outcomes can fail to identify a varying Boolean property. -/
example :
    ¬∃ descend :
        EmpiricalQuotient (fun _ : Unit => fun _ : Bool => ()) → Bool,
      id = descend ∘ empiricalClass (fun _ : Unit => fun _ : Bool => ()) := by
  exact (empirical_identifiability
    (fun _ : Unit => fun _ : Bool => ()) (id : Bool → Bool)).2
      ⟨false, true, (by intro _; rfl), Bool.false_ne_true⟩

#print axioms empirical_identifiability

end D5.S3.ConceptDynamics.EmpiricalIdentifiability
