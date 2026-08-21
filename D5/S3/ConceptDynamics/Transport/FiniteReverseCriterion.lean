/- GID: D5/S3/ConceptDynamics/Transport/FiniteReverseCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/FiniteReverseCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Empty carry yields a unique descent on the effective image. -/

import Mathlib.Data.Set.Image
import Mathlib.Data.Fintype.Basic

/- Library-search audit trail (2026-08-21).
   * `rg -n -i 'finite reverse|reverse criterion|effective.image.*unique|
     unique.*effective.image|carry.*empty|empty.*carry|Set\.range.*∃!|∃!.*Set\.range|
     range.*factor' D5 -g '*.lean'` found no existing theorem with this conclusion.
   * `rg -n -i 'rangeFactor|range.*factor|factor.*range|Surjective.*existsUnique|
     existsUnique.*Surjective|surjective.*unique|unique.*surjective'
     .lake/packages/mathlib/Mathlib -g '*.lean'` found the exact reusable range primitives
     `Set.rangeFactorization`, `Set.rangeFactorization_surjective`, and `Set.rangeSplitting`,
     but no theorem packaging carry-freeness as the required unique descent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Transport.FiniteReverseCriterion

/-- A carry records two states identified by the current readout but separated by the
future readout after the process. -/
def Carry {X Y BC BD : Type*} (F : X → Y) (qC : X → BC) (qD : Y → BD) : Type _ :=
  { states : X × X //
    qC states.1 = qC states.2 ∧ qD (F states.1) ≠ qD (F states.2) }

/-- A descent on the effective image makes the process/readout square commute at every
realized current value. -/
def EffectiveImageDescent {X Y BC BD : Type*} (F : X → Y) (qC : X → BC)
    (qD : Y → BD) (descent : Set.range qC → BD) : Prop :=
  ∀ x, descent (Set.rangeFactorization qC x) = qD (F x)

/-- In a finite decidable model, an empty carry type determines one and only one descent
from the effective image of the current readout to the future readout type. -/
theorem finite_reverse_criterion
    {X Y BC BD : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype BC] [DecidableEq BC]
    [Fintype BD] [DecidableEq BD]
    (F : X → Y) (qC : X → BC) (qD : Y → BD)
    (carryEmpty : IsEmpty (Carry F qC qD)) :
    ∃! descent : Set.range qC → BD, EffectiveImageDescent F qC qD descent := by
  let descent : Set.range qC → BD := fun b ↦ qD (F (Set.rangeSplitting qC b))
  have hDescent : EffectiveImageDescent F qC qD descent := by
    intro x
    have hq : qC (Set.rangeSplitting qC (Set.rangeFactorization qC x)) = qC x := by
      simpa using Set.apply_rangeSplitting qC (Set.rangeFactorization qC x)
    by_contra hne
    exact carryEmpty.false
      ⟨(Set.rangeSplitting qC (Set.rangeFactorization qC x), x), hq, hne⟩
  refine ⟨descent, hDescent, ?_⟩
  intro candidate hCandidate
  funext b
  obtain ⟨x, hx⟩ := b.property
  have hb : Set.rangeFactorization qC x = b := Subtype.ext hx
  rw [← hb]
  exact (hCandidate x).trans (hDescent x).symm

/-- A concrete finite model shows that the hypotheses and effective image are inhabited. -/
example :
    ∃! descent : Set.range (fun x : Bool ↦ x) → Bool,
      EffectiveImageDescent (fun x : Bool ↦ x) (fun x : Bool ↦ x)
        (fun x : Bool ↦ x) descent := by
  apply finite_reverse_criterion
  constructor
  rintro ⟨⟨x, y⟩, hxy, hne⟩
  exact hne hxy

example : Set.range (fun x : Bool ↦ x) := ⟨true, true, rfl⟩

#print axioms finite_reverse_criterion

end D5.S3.ConceptDynamics.Transport.FiniteReverseCriterion
