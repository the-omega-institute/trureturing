/- GID: D5/S3/ConceptDynamics/ConceptFiberDecomposition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ConceptFiberDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every concept readout decomposes its source into dependent fibers. -/

import Mathlib.Logic.Equiv.Sum

/- Library-search audit trail (2026-08-20):
   * `rg -n -F 'concept_fiber_decomposition' D5 Golden/Frozen/accepted` hit only
     this untracked candidate, so no accepted duplicate exists.
   * `rg -n 'Sigma.*Subtype|Subtype.*Sigma|Equiv.*Sigma|Sigma.*Equiv' D5 --glob '*.lean'`
     found only finite counting/use sites, not this arbitrary-readout decomposition.
   * `rg -n 'PSigma.*Equiv|Equiv.*PSigma|sigmaFiber|fiber.*equiv|equiv.*fiber'`
     found `Equiv.sigmaFiberEquiv`, the upstream subtype-fiber decomposition,
     and `Equiv.psigmaEquivSubtype`, which are reused below rather than reproved.
   * The deposited statement uses the source's proof-relevant `PSigma` fiber;
     `Equiv.sigmaCongrRight` transports the upstream subtype theorem to it. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- A concept is a readout from a type of objects to a type of coordinates. -/
def Concept (X B : Type _) := X → B

/-- The residual/余纤维 over a coordinate b of a concept readout. -/
def ConceptFiber {X B : Type _} (q_C : Concept X B) (b : B) :=
  PSigma (fun x : X => q_C x = b)

/-- The canonical dependent-sum decomposition of a type by any concept readout. -/
theorem concept_fiber_decomposition
    {X B : Type _} (q_C : Concept X B) :
    Nonempty (X ≃ Σ b : B, ConceptFiber q_C b) := by
  refine ⟨((Equiv.sigmaCongrRight fun b =>
    Equiv.psigmaEquivSubtype (fun x : X => q_C x = b)).trans
      (Equiv.sigmaFiberEquiv q_C)).symm⟩

example :
    Nonempty (Fin 2 ≃ Σ b : Bool, ConceptFiber (fun _ : Fin 2 => true) b) :=
  concept_fiber_decomposition (fun _ : Fin 2 => true)

#print axioms concept_fiber_decomposition

end D5.S3.ConceptDynamics.ConceptFiberDecomposition
