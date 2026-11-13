# Danskin directional derivative of a compact envelope

## Abstract

The compact convex envelope has a right directional derivative attained by an optimizer and dominating every optimizer derivative.

**Theorem 1.1 (An attaining maximal optimizer derivative).**

Lean statement: `D5/S3/Analytic/Convexity/Danskin.hasRightDirDeriv_iSup`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/Danskin.hasRightDirDeriv_iSup` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib Danskin directional derivative of a compact envelope*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Math/Analysis/Danskin.lean>.

*Commentary.*

Let E be any real inner product space, Z any nonempty compact topological space, and X an open convex subset of E. For jointly continuous f on X times Z, convex in its E argument, suppose each optimizer at x has a right directional derivative in direction v. The supremum value function has such a derivative d. One optimizer attains d, and every optimizer derivative is at most d. Completeness of E, separation axioms on Z and uniqueness of optimizers are not premises.

This is a faithful extraction of Daniel Lyng's Danskin.hasRightDirDeriv_iSup from Econlib at immutable revision d7bd9477476cade1c6695c8891746048ceddc52f, Econlib/Math/Analysis/Danskin.lean. Its original proof and live support are retained; the project header, imports and module visibility syntax are adapted. The original copyright and complete Apache 2.0 license are retained in docs/reports/licenses/econlib-Danskin-LICENSE.txt. No Optlib source is retained. The mathematical proof is attributed to the upstream author; repository integration supplies the stated adaptations.

For continuous real b and h on a nonempty compact subset K of an arbitrary topological space, use the compact subtype K as Z, E equal to the reals, X equal to the whole real line, x=0, v=1 and f(s,z)=b(z)+s*h(z). Joint continuity follows from continuity of b and h; the parameter fibers are affine. Their directional derivatives are h(z). Attainment and domination identify d with the maximum of h on the full argmax of b. Subtracting t*d from the increment gives a remainder little-o of t on the literal filter t tending to zero from above. Apply the same theorem to -b and -h and negate the output to obtain the minimum formula with the minimum of h on the full argmin of b. All optimizer ties remain. These are application correspondences, not additional named declarations or an independent proof, and add no metric or finite-domain premise.

Write M(t)=max_K(b+t*h), m(t)=min_K(b+t*h), U=argmax_K b and L=argmin_K b, where U and L contain every tied optimizer. On nhdsWithin 0 (Ioi 0), the remainders M(t)-M(0)-t*max_U h and m(t)-m(0)-t*min_L h are little-o of t. For the left side, replace only the perturbation h by -h and compose the parameter with t mapped to -t. On the literal filter nhdsWithin 0 (Iio 0), the corresponding coefficients are min_U h for M and max_L h for m. The compact set and the unperturbed functions' full optimizer sets are unchanged.

Subtract the two envelope expansions for the oscillation W(t)=M(t)-m(t). Its right coefficient is max_U h-min_L h, and its left coefficient is min_U h-max_L h. For any of these six expansions with coefficient c different from zero, the increment divided by t tends to c. Thus eventually c*(increment)>0 on the positive side and c*(increment)<0 on the negative side: the increment has the coefficient's sign on the right and its opposite on the left. A zero coefficient gives no strict sign conclusion; the constant family already has zero remainder and zero increment. These consequences require neither a unique optimizer nor any choice of a finite subset of optimizers.

Retire this extraction when this repository's own resolved Mathlib pin contains an equivalent general declaration with the full telescope and attaining/dominating conclusion, and both generic compact-subtype affine applications compile to the literal right maximum and minimum little-o expansions with the stated premises. Upstream acceptance alone is not the retirement condition.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/Danskin.hasRightDirDeriv_iSup`
