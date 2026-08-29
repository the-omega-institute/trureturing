/- GID: D5/S3/Analytic/Adelic/CuspidalToroidalKernel
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/CuspidalToroidalKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: All normalized cuspidal torus periods vanish exactly at a zero central value. -/

import Mathlib.Data.Complex.Basic

/- Library-search audit trail (2026-08-29):
   * Repository searches for cuspidal toroidal kernels, central-value criteria,
     Waldspurger identities, test vectors, and simultaneous torus-period
     vanishing found no exact frozen theorem or canonical period structure.
   * Body-shape searches for a complex period norm square equal to a local
     factor times central and twisted values found no D5 primitive. The public
     statement therefore exposes those source quantities as inputs and the
     norm-square identity as a hypothesis; no `def` or `abbrev` is introduced.
   * Pinned Mathlib has no automorphic-period theorem. Its exact constituent
     `Complex.normSq_eq_zero` identifies vanishing norm square with vanishing
     complex period, while `div_eq_zero_iff` and `mul_eq_zero` supply the
     nonzero-factor cancellation used below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Adelic.CuspidalToroidalKernel

/--
Under the normalized Waldspurger identity and a nonvanishing local twisted
test-vector witness, every quadratic-torus period vanishes exactly when the
base central value vanishes.
-/
theorem cuspidal_all_torus_kernel {Index : Type*}
    (period : Index -> ℂ)
    (localFactor twistedCentralValue : Index -> ℝ)
    (centralValue adjointValue : ℝ)
    (waldspurgerIdentity : ∀ index,
      Complex.normSq (period index) =
        localFactor index * (centralValue * twistedCentralValue index) /
          adjointValue)
    (adjointNonzero : adjointValue ≠ 0)
    (nonvanishingWitness : ∃ index,
      localFactor index ≠ 0 ∧ twistedCentralValue index ≠ 0) :
    (∀ index, period index = 0) ↔ centralValue = 0 := by
  constructor
  · intro invisible
    obtain ⟨index, localNonzero, twistNonzero⟩ := nonvanishingWitness
    have ratioZero :
        localFactor index * (centralValue * twistedCentralValue index) /
            adjointValue = 0 := by
      rw [← waldspurgerIdentity index, invisible index]
      exact Complex.normSq_zero
    have numeratorZero :
        localFactor index * (centralValue * twistedCentralValue index) = 0 :=
      (div_eq_zero_iff.mp ratioZero).resolve_right adjointNonzero
    have centralTimesTwistZero :
        centralValue * twistedCentralValue index = 0 :=
      (mul_eq_zero.mp numeratorZero).resolve_left localNonzero
    exact (mul_eq_zero.mp centralTimesTwistZero).resolve_right twistNonzero
  · intro centralZero index
    apply Complex.normSq_eq_zero.mp
    rw [waldspurgerIdentity index, centralZero]
    simp

example :
    ∃ (period : Unit -> ℂ)
      (localFactor twistedCentralValue : Unit -> ℝ)
      (centralValue adjointValue : ℝ),
      (∀ index,
        Complex.normSq (period index) =
          localFactor index * (centralValue * twistedCentralValue index) /
            adjointValue) ∧
        adjointValue ≠ 0 ∧
        ∃ index,
          localFactor index ≠ 0 ∧ twistedCentralValue index ≠ 0 := by
  refine ⟨fun _ => 0, fun _ => 1, fun _ => 1, 0, 1, ?_, one_ne_zero,
    (), one_ne_zero, one_ne_zero⟩
  intro index
  simp

#print axioms cuspidal_all_torus_kernel

end D5.S3.Analytic.Adelic.CuspidalToroidalKernel
