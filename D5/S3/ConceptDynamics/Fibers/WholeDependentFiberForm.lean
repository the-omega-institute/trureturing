/- GID: D5/S3/ConceptDynamics/Fibers/WholeDependentFiberForm
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Fibers/WholeDependentFiberForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Any readout decomposes its source into its dependent coordinate fibers. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition

/- Library-search audit trail (2026-08-22):
   * `rg -n -i 'sigma.*fiber|fiber.*sigma|dependent.*fiber|total.*fiber|equiv.*fiber'
     D5 Blueprint --glob '*.lean' --glob '*.md'` found the canonical family module
     `D5.S3.ConceptDynamics.ConceptFiberDecomposition`, whose `Concept` and
     `ConceptFiber` source carriers are imported below.
   * The family's theorem has the same equivalence signature, but its printed
     closure includes `Classical.choice`; it therefore does not cover the source's
     explicit no-choice clause.
   * Pinned Mathlib's `Equiv.sigmaFiberEquiv` is the exact choice-free decomposition
     primitive. It is applied directly in `wholeFiberEquiv`, with an explicit
     transport from subtype fibers to the family's proof-relevant fibers.
   * The public signature has arbitrary types and an arbitrary readout. It assumes
     no quotient object, surjectivity, section, linear structure, or metric.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Fibers.WholeDependentFiberForm

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

private def wholeFiberEquiv
    {X B : Type _} (q : Concept X B) :
    X ≃ Σ b : B, ConceptFiber q b where
  toFun x :=
    let z := (Equiv.sigmaFiberEquiv q).symm x
    ⟨z.1, ⟨z.2.1, z.2.2⟩⟩
  invFun z := Equiv.sigmaFiberEquiv q ⟨z.1, ⟨z.2.1, z.2.2⟩⟩
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨b, x, h⟩
    cases h
    rfl

/-- Every object consists of its coordinate together with its position in the
dependent fiber over that coordinate. -/
theorem whole_dependent_fiber_form
    {X B : Type _} (q : Concept X B) :
    Nonempty (X ≃ Σ b : B, ConceptFiber q b) := by
  exact ⟨wholeFiberEquiv q⟩

#print axioms whole_dependent_fiber_form

end D5.S3.ConceptDynamics.Fibers.WholeDependentFiberForm
