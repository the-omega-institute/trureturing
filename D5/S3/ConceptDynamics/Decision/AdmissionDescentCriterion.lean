/- GID: D5/S3/ConceptDynamics/Decision/AdmissionDescentCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Decision/AdmissionDescentCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize admission descent by fibers, boundaries, cores, and hulls. -/

import D5.S0.Rewriting.Quotients.AnswerabilityCriterion

/- Library-search audit trail (2026-09-04):
   * Repository searches for admission descent, universal fiber cores, existential fiber hulls,
     mixed-fiber boundaries, and generalized quotient factorization found the exact existing
     factorization/fiber/empty-defect theorem `AnswerabilityCriterion.answerability_criterion`.
   * That theorem is imported and applied below rather than reproved. Repository searches found
     no result adjoining the simultaneous universal-core and existential-hull equalities.
   * Exact pinned-Mathlib hit `Function.factorsThrough_iff`, already used by the imported theorem,
     remains the unique factorization source. The new proof uses only set extensionality,
     propositional extensionality, and explicit representatives of the current fiber.
-/

namespace D5.S3.ConceptDynamics.Decision.AdmissionDescentCriterion

open D5.S0.Rewriting.Quotients.AnswerabilityCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- An admission set is constant on every fiber of the visible quotient. -/
def FiberConstant {X B : Type*} (q : X → B) (admitted : Set X) : Prop :=
  ∀ ⦃x y : X⦄, q x = q y → (x ∈ admitted ↔ y ∈ admitted)

/-- The mixed-fiber boundary consists of same-readout pairs with different admission status. -/
def admissionBoundary {X B : Type*} (q : X → B) (admitted : Set X) : Set (X × X) :=
  {pair | q pair.1 = q pair.2 ∧ (pair.1 ∈ admitted) ≠ (pair.2 ∈ admitted)}

/-- States whose entire visible fiber is admitted. -/
def universalFiberCore {X B : Type*} (q : X → B) (admitted : Set X) : Set X :=
  {x | ∀ y, q y = q x → y ∈ admitted}

/-- States whose visible fiber contains an admitted representative. -/
def existentialFiberHull {X B : Type*} (q : X → B) (admitted : Set X) : Set X :=
  {x | ∃ y ∈ admitted, q y = q x}

/-- Fiber constancy is exactly simultaneous equality with the universal fiber core and the
existential fiber hull. Both directions are explicit: the forward direction uses the current
state as a fiber representative, while the reverse direction reads constancy from the core. -/
theorem fiberConstant_iff_core_eq_and_hull_eq
    {X B : Type*} (q : X → B) (admitted : Set X) :
    FiberConstant q admitted ↔
      admitted = universalFiberCore q admitted ∧ admitted = existentialFiberHull q admitted := by
  constructor
  · intro hconstant
    constructor
    · ext x
      constructor
      · intro hx y hy
        exact (hconstant hy.symm).mp hx
      · intro hx
        exact hx x rfl
    · ext x
      constructor
      · intro hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, hq⟩
        exact (hconstant hq).mp hy
  · rintro ⟨hcore, _hhull⟩ x y hq
    constructor
    · intro hx
      have hxCore : x ∈ universalFiberCore q admitted := hcore ▸ hx
      exact hxCore y hq.symm
    · intro hy
      have hyCore : y ∈ universalFiberCore q admitted := hcore ▸ hy
      exact hyCore x hq

/-- The four clauses of the admission descent criterion are equivalent: admission factors through
the visible quotient, is constant on every quotient fiber, has empty mixed-fiber boundary, and is
simultaneously its universal fiber core and existential fiber hull. -/
theorem admission_descent_criterion
    {X B : Type*} (anchor : X) (q : X → B) (admitted : Set X) :
    ((∃ descended : B → Prop, ∀ x, x ∈ admitted ↔ descended (q x)) ↔
        FiberConstant q admitted) ∧
      (FiberConstant q admitted ↔ admissionBoundary q admitted = ∅) ∧
      (FiberConstant q admitted ↔
        admitted = universalFiberCore q admitted ∧
          admitted = existentialFiberHull q admitted) := by
  have hcriterion := answerability_criterion anchor q (fun x => x ∈ admitted)
  have hfactorForm :
      (∃ descended : B → Prop, ∀ x, x ∈ admitted ↔ descended (q x)) ↔
        ∃ descended : B → Prop, (fun x => x ∈ admitted) = descended ∘ q := by
    constructor
    · rintro ⟨descended, hdescended⟩
      refine ⟨descended, funext fun x => ?_⟩
      exact propext (hdescended x)
    · rintro ⟨descended, hdescended⟩
      refine ⟨descended, fun x => ?_⟩
      have hx := congrFun hdescended x
      simpa [Function.comp_apply] using Iff.of_eq hx
  have hfiberForm :
      (∀ ⦃x y : X⦄, q x = q y → (x ∈ admitted) = (y ∈ admitted)) ↔
        FiberConstant q admitted := by
    constructor
    · intro h x y hq
      exact Iff.of_eq (h hq)
    · intro h x y hq
      exact propext (h hq)
  have hfactor :
      (∃ descended : B → Prop, ∀ x, x ∈ admitted ↔ descended (q x)) ↔
        FiberConstant q admitted :=
    hfactorForm.trans (hcriterion.1.trans hfiberForm)
  have hboundary : FiberConstant q admitted ↔ admissionBoundary q admitted = ∅ := by
    rw [← hfiberForm]
    simpa only [admissionBoundary] using hcriterion.2.1
  exact ⟨hfactor, hboundary, fiberConstant_iff_core_eq_and_hull_eq q admitted⟩

#print axioms fiberConstant_iff_core_eq_and_hull_eq
#print axioms admission_descent_criterion

end D5.S3.ConceptDynamics.Decision.AdmissionDescentCriterion
