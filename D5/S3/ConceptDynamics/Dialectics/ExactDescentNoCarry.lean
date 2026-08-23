/- GID: D5/S3/ConceptDynamics/Dialectics/ExactDescentNoCarry
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Dialectics/ExactDescentNoCarry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact descent through two readouts excludes every carry witness. -/

import D5.S3.ConceptDynamics.Dialectics.MinimalDialecticalRepair

/- Library-search audit trail (2026-08-22):
   * The repository's frozen `IsCarryWitness` is the exact family primitive for
     equal current readouts and unequal processed target readouts; it is reused.
   * The frozen `dynamics_descends_iff` is adjacent but assumes one surjective
     quotient presentation and a self-map, so it does not cover two arbitrary readouts.
   * Pinned Mathlib supplies the exact fiber predicate `Function.FactorsThrough`,
     but no exact descent-to-no-carry wrapper. Loogle returned no exact theorem,
     and LeanSearch returned only unrelated quotient-map results. -/

namespace D5.S3.ConceptDynamics.Dialectics.ExactDescentNoCarry

open D5.S3.ConceptDynamics.Dialectics.MinimalDialecticalRepair

example : Nonempty Bool := ⟨false⟩

example :
    ∃ (qX : Bool → Unit) (qY : Bool → Bool) (flow : Bool → Bool)
      (descended : Unit → Bool),
      qY ∘ flow = descended ∘ qX := by
  refine ⟨fun _ => (), fun _ => false, id, fun _ => false, ?_⟩
  funext state
  rfl

example :
    IsCarryWitness (fun _ : Bool => ()) (id : Bool → Bool) (id : Bool → Bool)
      false true :=
  booleanCarry

/-- If a flow commutes exactly with source and target readouts through a descended
map, then no pair in one source fiber can become distinguishable at the target. -/
theorem exact_descent_has_no_carry
    {X Y B C : Type*} (qX : X → B) (qY : Y → C) (flow : X → Y)
    (descended : B → C) (hDescent : qY ∘ flow = descended ∘ qX) :
    ∀ {left right : X},
      ¬IsCarryWitness qX (id : X → X) (qY ∘ flow) left right := by
  intro left right witness
  apply witness.2
  calc
    (qY ∘ flow) (id left) = (descended ∘ qX) left := congrFun hDescent left
    _ = (descended ∘ qX) right := congrArg descended witness.1
    _ = (qY ∘ flow) (id right) := (congrFun hDescent right).symm

#print axioms exact_descent_has_no_carry

end D5.S3.ConceptDynamics.Dialectics.ExactDescentNoCarry
