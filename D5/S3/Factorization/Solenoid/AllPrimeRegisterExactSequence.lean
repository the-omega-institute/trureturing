/- GID: D5/S3/Factorization/Solenoid/AllPrimeRegisterExactSequence
   generality: I
   mirror-B: D5/B/S3/Factorization/Solenoid/AllPrimeRegisterExactSequence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Package the all-prime register as a short exact sequence with prime-adic kernel. -/

import D5.S3.Factorization.SolenoidProfiniteKernel

/- Library-search audit trail (2026-08-16):
   * Pinned Mathlib searches for solenoids, profinite integers, and the
     Pontryagin dual of the rationals found no matching declaration.
   * Loogle found no declaration for `PontryaginDual Rat`; its bare
     `solenoid` query reported an unknown identifier.
   * Repository search found the exact all-prime support theorem
     `universal_solenoid_profinite_exact`; it is imported and applied below.
-/

namespace D5.S3.Factorization.Solenoid.AllPrimeRegisterExactSequence

open D5.S1.Dynamics
open D5.S3.Factorization.SolenoidProfiniteKernel

/-- The all-prime register has an injective hidden-fiber inclusion, is exact
at the universal solenoid, surjects onto the visible circle, and has one
prime-adic integer coordinate in its kernel for every prime. -/
theorem all_prime_register_short_exact :
    Function.Injective
        ((↑) : UniversalSolenoid.projection.ker → UniversalSolenoid) ∧
      Function.Exact
        ((↑) : UniversalSolenoid.projection.ker → UniversalSolenoid)
        UniversalSolenoid.projection ∧
      Function.Surjective UniversalSolenoid.projection ∧
      Function.Bijective profiniteKernelEquiv := by
  refine ⟨Subtype.val_injective, ?_⟩
  exact universal_solenoid_profinite_exact

#print axioms all_prime_register_short_exact

end D5.S3.Factorization.Solenoid.AllPrimeRegisterExactSequence
