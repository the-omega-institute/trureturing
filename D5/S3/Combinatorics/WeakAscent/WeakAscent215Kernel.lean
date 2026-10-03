/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215Kernel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215Kernel
   mirror-E: none(waiver:constructive-left-kernel-series)
   anchors: [mathlib/module/Mathlib.RingTheory.MvPowerSeries.Equiv]
   utility: none
   digest: Recursive coefficients construct and uniquely identify the target series. -/

import Mathlib.RingTheory.MvPowerSeries.Equiv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215Kernel

open Finset PowerSeries

noncomputable def positiveStep {R : Type*} [CommSemiring R]
    (tail : PowerSeries R) : PowerSeries R :=
  (1 + X * tail) ^ 2 + X ^ 2 * ((1 + X * tail) ^ 2 * tail)

noncomputable def kernelCoefficients : ℕ → ℕ :=
  Nat.strongRec fun degree previous =>
    coeff degree (positiveStep (mk fun index =>
      if lower : index < degree then previous index lower else 0))

noncomputable def targetSeries : PowerSeries ℚ :=
  1 + X * mk fun degree => (kernelCoefficients degree : ℚ)

noncomputable def smallRootCoefficients (kernel : MvPowerSeries (Option Unit) ℚ) : ℕ → ℚ :=
  Nat.strongRec fun degree previous =>
    coeff degree (X + X ^ 2 * kernel.subst (fun position =>
      if position = some () then X else
        mk fun index => if lower : index < degree then previous index lower else 0))

noncomputable def smallRoot (kernel : MvPowerSeries (Option Unit) ℚ) : PowerSeries ℚ :=
  mk (smallRootCoefficients kernel)

end D5.S3.Combinatorics.WeakAscent.WeakAscent215Kernel
