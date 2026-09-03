/- GID: D5/S3/ConceptDynamics/CanonicalImage/FiniteObservationQuotientRange
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CanonicalImage/FiniteObservationQuotientRange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite joint-readout quotient is equivalent to its realized image. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-09-03):
   * The current-tree `jointReadout` is the canonical dependent product readout
     and is imported rather than redeclared.
   * Pinned Mathlib and live Loogle both return the exact arbitrary-function
     theorem `Setoid.quotientKerEquivRange`; the main theorem applies it directly.
   * The current-tree linear `FiniteReadoutKernel` and the stronger
     `CompletionCriterion` do not carry this atom's finite dependent budget
     with exactly its single equivalence conclusion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CanonicalImage.FiniteObservationQuotientRange

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w

/-- The dependent output product `O_J` from source lines 476-483. -/
abbrev FiniteObservationOutput {I : Type u} (O : I -> Type w)
    (J : Finset I) : Type (max u w) :=
  forall j : J, O j.1

/-- The finite-budget joint readout `q_J` from source lines 476-483. -/
def finiteObservationReadout {I : Type u} {X : Type v} {O : I -> Type w}
    (q : forall i, X -> O i) (J : Finset I) :
    X -> FiniteObservationOutput O J :=
  jointReadout (fun j : J => q j.1)

/-- Static relative identity `sim_J` from source lines 486-493. -/
def staticRelativeIdentity {I : Type u} {X : Type v} {O : I -> Type w}
    (q : forall i, X -> O i) (J : Finset I) : Setoid X :=
  Setoid.ker (finiteObservationReadout q J)

/-- The effective observation quotient `Z_J` from source lines 516-519. -/
abbrev EffectiveObservationQuotient {I : Type u} {X : Type v}
    {O : I -> Type w} (q : forall i, X -> O i) (J : Finset I) :=
  Quotient (staticRelativeIdentity q J)

/-- The effective observation quotient is canonically equivalent to the
realized image of the finite-budget joint readout (source lines 522-530). -/
theorem finite_observation_quotient_equiv_range
    {I : Type u} {X : Type v} {O : I -> Type w}
    (q : forall i, X -> O i) (J : Finset I) :
    Nonempty
      (EffectiveObservationQuotient q J ≃
        Set.range (finiteObservationReadout q J)) :=
  ⟨Setoid.quotientKerEquivRange (finiteObservationReadout q J)⟩

-- Satisfiability: a singleton budget with a constant readout is non-injective.
example :
    ¬Function.Injective
      (finiteObservationReadout
        (fun _ : Unit => fun _ : Bool => ()) ({()} : Finset Unit)) := by
  intro injective
  exact Bool.false_ne_true (injective rfl)

example :
    Nonempty
      (EffectiveObservationQuotient
          (fun _ : Unit => fun _ : Bool => ()) ({()} : Finset Unit) ≃
        Set.range
          (finiteObservationReadout
            (fun _ : Unit => fun _ : Bool => ()) ({()} : Finset Unit))) :=
  finite_observation_quotient_equiv_range _ _

-- Reverse probe: the public equivalence transfers inhabitation in both directions.
example {I : Type u} {X : Type v} {O : I -> Type w}
    (q : forall i, X -> O i) (J : Finset I) :
    Nonempty (EffectiveObservationQuotient q J) <->
      Nonempty (Set.range (finiteObservationReadout q J)) := by
  rcases finite_observation_quotient_equiv_range q J with ⟨equiv⟩
  exact equiv.nonempty_congr

-- The empty budget on `Unit` is intentionally legal: the source covers every function.
example :
    Nonempty
      (EffectiveObservationQuotient
          (fun _ : Empty => fun _ : Unit => ()) (∅ : Finset Empty) ≃
        Set.range
          (finiteObservationReadout
            (fun _ : Empty => fun _ : Unit => ()) (∅ : Finset Empty))) :=
  finite_observation_quotient_equiv_range _ _

#print axioms finite_observation_quotient_equiv_range

end D5.S3.ConceptDynamics.CanonicalImage.FiniteObservationQuotientRange
