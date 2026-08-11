/- GID: D5/S3/ObserverMemory/FiniteReadoutKernel
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FiniteReadoutKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A linear readout identifies its domain modulo its kernel with its attainable range. -/

import Mathlib.LinearAlgebra.Isomorphisms

/- Provenance: thin honest wrapper over pinned mathlib's first isomorphism
   theorem for modules, `LinearMap.quotKerEquivRange`. -/

namespace D5.S3.ObserverMemory.FiniteReadoutKernel

universe uR uM uN

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]

/--
A linear readout retains exactly its attainable values after differences in
its kernel are identified. This is a declared thin wrapper around mathlib's
`LinearMap.quotKerEquivRange`; the source atom's finite setting is not needed
for the module-theoretic statement.
-/
theorem finite_readout_quotient_equiv_range (readout : M →ₗ[R] N) :
    Nonempty ((M ⧸ LinearMap.ker readout) ≃ₗ[R] LinearMap.range readout) :=
  ⟨readout.quotKerEquivRange⟩

end D5.S3.ObserverMemory.FiniteReadoutKernel
