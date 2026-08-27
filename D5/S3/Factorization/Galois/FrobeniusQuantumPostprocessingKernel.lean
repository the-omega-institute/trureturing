/- GID: D5/S3/Factorization/Galois/FrobeniusQuantumPostprocessingKernel
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/FrobeniusQuantumPostprocessingKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Frobenius-observer fibers survive quantum encoding and deterministic observation. -/

import D5.S3.Factorization.Galois.GaloisPrimeObserver

/- Library-search audit trail (2026-08-28):
   * Exact repository hit `galoisPrimeObserver` is the canonical tagged
     Frobenius observer and is imported rather than redeclared.
   * Repository body-shape searches for its equality kernel under function
     composition found no theorem packaging this postprocessing statement.
   * Pinned Mathlib exact hits `Function.FactorsThrough.rfl` and
     `Function.FactorsThrough.comp_left` prove that arbitrary left composition
     preserves every source fiber; they are applied directly below.
   * Loogle and LeanSearch are unavailable on PATH in this worktree. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Galois.FrobeniusQuantumPostprocessingKernel

open D5.S3.Factorization.Galois.GaloisPrimeObserver

/-- Equal tagged Frobenius observations remain equal after any quantum-state
encoding and any deterministic downstream observation. -/
theorem frobenius_quantum_postprocessing_kernel
    {G : Type*} [Monoid G]
    (unramified : Nat.Primes -> Prop)
    (frobenius : forall p, unramified p -> G)
    {QuantumState Observation : Type*}
    (encode : Option (ConjClasses G) -> QuantumState)
    (observe : QuantumState -> Observation) :
    Setoid.ker (galoisPrimeObserver unramified frobenius) <=
      Setoid.ker
        (observe ∘ encode ∘ galoisPrimeObserver unramified frobenius) := by
  change Function.FactorsThrough
    (observe ∘ encode ∘ galoisPrimeObserver unramified frobenius)
    (galoisPrimeObserver unramified frobenius)
  exact Function.FactorsThrough.comp_left Function.FactorsThrough.rfl
    (observe ∘ encode)

#print axioms frobenius_quantum_postprocessing_kernel

end D5.S3.Factorization.Galois.FrobeniusQuantumPostprocessingKernel
