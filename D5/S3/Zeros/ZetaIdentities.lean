/- GID: D5/S3/Zeros/ZetaIdentities
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Expose the zeta residue, Dirichlet series, and Euler product identities. -/

import D5.S3.Weil.EulerProduct
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

namespace D5.S3.Zeros.ZetaIdentities

open Filter
open D5.S3.Weil.Convention
open scoped BigOperators Topology

/-- The residue of the repository's classical zeta reading at one is exactly one. -/
theorem riemann_zeta_residue_one :
    Tendsto (fun s : ℂ => (s - 1) * classicalZeta s) (𝓝[≠] 1) (𝓝 1) := by
  simpa [classicalZeta] using _root_.riemannZeta_residue_one

/-- The natural-number Dirichlet series equals the repository's zeta reading in its
absolute-convergence half-plane. -/
theorem riemann_zeta_dirichlet_sum (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ, (n : ℂ) ^ (-s)) = classicalZeta s := by
  simpa [riemannZetaSummandHom, classicalZeta] using tsum_riemannZetaSummand hs

/-- The prime-indexed Euler product equals the same zeta reading in the
absolute-convergence half-plane. -/
theorem riemann_zeta_euler_product (s : ℂ) (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹) = classicalZeta s := by
  simpa [classicalZeta] using riemannZeta_eulerProduct_tprod hs

end D5.S3.Zeros.ZetaIdentities
