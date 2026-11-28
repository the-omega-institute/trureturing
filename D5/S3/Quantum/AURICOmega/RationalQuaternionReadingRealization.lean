/- GID: D5/S3/Quantum/AURICOmega/RationalQuaternionReadingRealization
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/RationalQuaternionReadingRealization
   mirror-E: none(waiver:exact-symbolic-construction)
   anchors: []
   utility: none
   digest: Realize admissible signed contrasts by a rational kernel on an entire nonabelian group. -/

import OmegaMath.Geometry.QuaternionContrast

/-!
# Rational readings on a group

The three-point reading problem in Chapter 1 of *Omega Math* asks which observations can
coexist with bilateral transport. Here the quaternion group and its kernel may depend on the
prescribed mutual reading and signed contrast.
-/

namespace D5.S3.Quantum.AURICOmega.RationalQuaternionReadingRealization

open Omega.Geometry.QuaternionContrast (IsSeparatedBiInvariantKernel)

/-- A whole group realizes every rational pair with nonnegative overlap and squared contrast
at most one minus the overlap. The same kernel attains zero and separates its points. -/
theorem exists_rational_group_kernel_with_readings (t d : ℚ) (ht₀ : 0 ≤ t)
    (hd : d ^ 2 ≤ 1 - t) :
    ∃ (G : Type) (_ : Group G) (K : G → G → ℚ),
      IsSeparatedBiInvariantKernel K ∧ (∃ p : G, K 1 p = 0) ∧
      (∃ u v : G, u * v ≠ v * u) ∧ (∃ y z : G, K 1 y = t ∧ K 1 z - K y z = d) :=
  Omega.Geometry.QuaternionContrast.exists_rational_biinvariant_kernel t d ht₀ hd

end D5.S3.Quantum.AURICOmega.RationalQuaternionReadingRealization
