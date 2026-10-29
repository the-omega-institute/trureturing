# Actual asymmetric observation limits

## Abstract

Actual asymmetric observation limits

**Definition 1.1 (Independent chronological observation lengths).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.observation`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.observation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an integer-indexed Boolean path z and natural lengths l and r, observation(l,r,z) is the pair of the original chronological leftWord(l,z), on coordinates minus l through minus one, and rightWord(r,z), on coordinates one through r. The center is absent. Either length can be zero.

**Definition 1.2 (The actual conditional probability under one law).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.mean`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.mean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a probability measure mu on visible paths and a measurable observation o, mean(mu,o,z) evaluates the actual conditional distribution of z(0) given o at o(z), on the event that the center bit is true. The total conditional kernel supplies values even at null observation fibers. No limiting posterior is defined through an inequality or an inverse construction.

**Definition 1.3 (Almost-sure and L2 convergence).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.MeanSquareLimit`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.MeanSquareLimit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

MeanSquareLimit(mu,f,g) asserts almost-sure pointwise convergence of f(n) to g, membership of every f(n) and g in L2(mu), and convergence to zero of the integral of the squared difference. All measures in these assertions are the same mu.

**Theorem 1.4 (Both orders of completing the retained half-lines).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.ordered_half_line_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.ordered_half_line_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every probability mu on original integer-time visible paths and every natural retained length j, completing the left side of observation(k,n) converges almost surely and in L2 to the actual mean given the entire past and the first n future bits. Completing the right side of observation(n,k) converges in both senses to the actual mean given the last n past bits and the entire future. These two intermediate means, as n increases, each converge to the actual mean given the full exterior. With j fixed, observation(j,n) converges to the actual leftObservation(j) mean, and observation(n,j) to the actual rightObservation(j) mean. Thus both ordered completions retain exactly the source observation fields. For j zero, the opposite infinite half-line remains present. The proof reconstructs each infinite coordinate field from chronological finite observations, applies Levy upward convergence to the actual conditional expectations, and uses the uniform interval from zero to one to prove square-error convergence by dominated convergence. Finite and limiting means are explicitly in L2.

**Definition 1.5 (The original blocks ending at minus one).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.leftCount`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.leftCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a word w, block length b, retained length j and path z, leftCount is originalSuccessCount(w,b,j/b) on the chronological leftWord(j,z), after dropping the first j modulo b bits. Its full blocks are exactly the source intervals from minus q times b through minus one, where q is j/b. A full block contributes one if it contains any complete occurrence of w; overlapping occurrences in one block still contribute only one.

**Definition 1.6 (The original blocks starting at one).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.rightCount`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.rightCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rightCount is originalSuccessCount(w,b,j/b) on the chronological rightWord(j,z). Its full blocks start at one and each have length b. Neither count changes when observations outside the retained j bits are added.

**Theorem 1.7 (The original finite bound transfers to the full opposite half-line).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.same_law_counted_half_line_smoothing`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.same_law_counted_half_line_smoothing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be finite with measurable singletons, theta an original stationary binary edge presentation, and J any probability measure satisfying exactly theta's original marked-cylinder identities. Let w be nonempty and let its original word product have rectangular positive support R. Set mu to the visible pushforward of this same J, b to length(w) plus card(H), and rho to one minus the exact rectangleMinimum divided by rectangleMaximum. On one common mu-null-set convention, for every j, the absolute difference between the actual full-exterior mean and the actual leftObservation(j) mean is at most rho raised to leftCount(w,b,j,z); the corresponding rightObservation(j) difference is at most rho raised to rightCount(w,b,j,z). The finite_record_smoothing_by_original_success_count supplies both finite comparisons unchanged. Actual finite observation fibers equal the original chronological record cylinders. Outside their actual null fibers, conditional disintegration gives precisely recordPosterior, so the finite comparisons apply to actual conditional expectations. First the extra side tends to infinity, then the common opposite side tends to infinity, with the original count fixed. Countable intersections give the common null-set convention. No independence, row unifilarity, aperiodicity, global entrywise no11, extra positivity or posterior band is assumed. Structural zeros and zero-probability fibers are allowed. Natural powers retain rho zero and count zero, with the zeroth power equal to one. In particular j zero retains its entire opposite half-line.

For the positive-weight class C in the rectangular-word theorem, take H to be the original subtype C, theta to be nativeComponent, and J to be its original-cylinder law. component_restriction identifies its visible pushforward with the actual class-conditioned visible law. Keep the source w, its support rectangle, the exact minimum and maximum, and b equal to length(w) plus card(C). The two displayed inequalities are then the source full-half-line comparisons with the original block clocks. The theorem does not assert the separate explicit feasible-state kernel formulas, their common-mass minorization, or product telescoping identities. Nor does it establish chronological count-moment payment, risk summability, or the component-mixture tail conclusions.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.MeanSquareLimit`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.leftCount`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.mean`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.observation`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.ordered_half_line_limits`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.rightCount`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits.same_law_counted_half_line_smoothing`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ErasedExteriorFiltration](../ErasedExteriorFiltration.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleSmoothing](../OriginalRectangleSmoothing.md)
