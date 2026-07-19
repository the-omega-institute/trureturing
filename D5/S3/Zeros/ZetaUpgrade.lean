/- GID: D5/S3/Zeros/ZetaUpgrade
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Upgrade the zeta sum-product identity and its unique simple pole receipt. -/

import D5.S3.Zeros.ZetaIdentities

namespace D5.S3.Zeros.ZetaUpgrade

open Filter
open D5.S3.Weil.Convention
open scoped BigOperators Topology

/-- A function is analytic away from one named point and has a nonzero
first Laurent coefficient there. -/
def HasUniqueSimplePoleWithResidue (f : ℂ -> ℂ) (z residue : ℂ) : Prop :=
  AnalyticOnNhd ℂ f ({z}ᶜ) ∧
    Tendsto (fun s => (s - z) * f s) (𝓝[≠] z) (𝓝 residue) ∧
    residue ≠ 0

/-- The Dirichlet series and prime Euler product are directly equal in their
common half-plane of absolute convergence. -/
theorem riemann_zeta_dirichlet_sum_eq_euler_product (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ, (n : ℂ) ^ (-s)) =
      ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ := by
  calc
    (∑' n : ℕ, (n : ℂ) ^ (-s)) = classicalZeta s :=
      ZetaIdentities.riemann_zeta_dirichlet_sum s hs
    _ = ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ :=
      (ZetaIdentities.riemann_zeta_euler_product s hs).symm

/-- The classical zeta reading is analytic away from one and has residue one
at its unique simple pole. -/
theorem classical_zeta_unique_simple_pole_residue_one :
    HasUniqueSimplePoleWithResidue classicalZeta 1 1 := by
  constructor
  · simpa [classicalZeta] using analyticOn_riemannZeta
  constructor
  · simpa [classicalZeta] using _root_.riemannZeta_residue_one
  · norm_num

end D5.S3.Zeros.ZetaUpgrade
