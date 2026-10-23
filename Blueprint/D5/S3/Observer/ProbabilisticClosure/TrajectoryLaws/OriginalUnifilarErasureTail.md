# All-stationary geometric erasure tail

## Abstract

All-stationary geometric erasure tail

**Theorem 1.1 (A specified blocked geometric tail).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarErasureTail.tail_series`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarErasureTail.tail_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative D and rho with rho less than one, positive natural ell, and every natural R, the real series D*rho^((R+n)/ell) is summable and its sum is at most D*ell/(1-rho)*rho^(R/ell). Natural division retains the first partial block. TwelveStateTail consumes the unchanged original supplier at D=5/2 and ell=2.

Use the same finite original theta, selected bilateral J and actual visible pushforward P as OriginalUnifilarQuotient. The only new restriction is RowUnifilar after positive-mass trimming. The universal OriginalErasureComparison.full_half_line_erasure_comparison remains unrestricted and is applied directly. All radii, cuts and lengths are original emitted-bit integers or natural numbers, not a stopped or rescaled clock.

**Definition 1.2 (Original-clock geometric tail allowance).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarErasureTail.allowance`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarErasureTail.allowance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real D,rho and natural ell,R, allowance(D,rho,ell,R)=2*D*ell/(1-rho)*rho^(R/ell). Its uses have D>=0, ell>=1 and 0<=rho<1. The quotient R/ell is natural division. The first partial length-ell block is overcounted, preserving radius zero and the initial finite tail when rho=0.

**Theorem 1.3 (Actual errors, finite tails and vanishing).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarErasureTail.all_stationary_geometric_allowance`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarErasureTail.all_stationary_geometric_allowance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original theta with measurable hidden singletons and retained-row unifilarity, put D=pairWeight(classWeight(trim(theta))). There exist natural ell>=1 and real 0<=rho<1 such that for every r, actual classError(theta,r)<=ofReal(D*rho^(r/ell)), leftRisk(theta,r)<=D*rho^(r/ell), and rightRisk(theta,r)<=D*rho^(r/ell). For every R, the original ENNReal erasureTail(theta,R) is at most ofReal(allowance(D,rho,ell,R)) and is not infinite. The real series of leftRisk+rightRisk is summable. Both the real allowance and the ENNReal erasure tail tend to zero as R tends to infinity.

Apply actual_geometric_classification on the same theta, J and P. The existing full_half_line_erasure_comparison bounds both actual squared risks by that actual classError and bounds the extended nonnegative tail by twice its series. No unifilarity is introduced into that supplier. Nonnegativity of each real squared integral justifies comparison and summability.

Group the normalized majorant rho^(n/ell) by the exact bijection Nat.divModEquiv(ell): naturals to naturals times Fin ell. The existing geometric-series theorem gives total ell/(1-rho). Since (R+n)/ell is at least R/ell+n/ell and 0<=rho<=1, each shifted term is bounded by rho^(R/ell)*rho^(n/ell). Multiply by D, sum and retain the entire first partial block. Monotonicity and ofReal_tsum_of_nonneg transfer the finite real upper bound to the previously possibly infinite ENNReal tail. No finite numerical test proves or replaces this infinite conclusion.

The natural quotient R/ell tends to infinity, so the geometric factor tends to zero; multiplication by the finite constant gives vanishing allowance. The ENNReal tail tends to zero by squeezing. If rho=0, natural exponent zero gives 0^0=1, while every r>=ell has positive exponent: class errors and both risks are exactly zero there. The initial tail remains bounded by 2*D*ell. If K=1, the cardinal bound and nonnegativity give D=0; every class error, both defects, every erasure tail and the allowance are exactly zero at every radius, including zero.

The theorem covers reducible and periodic stationary presentations, zero-probability symbols, impossible words and original zero-mass nonunifilar rows. It adds no ergodicity, reversal, positive original masses or synchronization assumption. The constants belong to this fixed actual law and chosen presentation. Source sections 4 onward, strict-scope witnesses, stopping and arbitrary-finite attainment or separation questions are outside this theorem.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarErasureTail.all_stationary_geometric_allowance`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarErasureTail.allowance`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarErasureTail.tail_series`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient](OriginalUnifilarQuotient.md)
