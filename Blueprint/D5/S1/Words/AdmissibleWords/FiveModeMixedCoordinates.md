# Mixed coordinates of the five-mode simplex

## Abstract

The three site occupancies and the log cross-ratio of the base corners form a global chart of the positive five-mode laws, and the base loop is the Fisher gradient of the cross-ratio.

A five-mode law is a probability vector p = (p_O, p_L, p_T, p_R, p_J) on the admissible words 000, 100, 010, 001, 101. Its visible point is (X, Y, Z) = (p_L + p_J, p_R + p_J, p_T), the occupancies of the first, last and middle sites. The hidden coordinate is chi = log(p_O p_J / (p_L p_R)), and the base loop is d = (1, -1, 0, -1, 1). The Fisher inner product at p is the sum over modes of u_s v_s / p_s.

Fix the correspondence (O,L,T,R,J) = (2,3,5,7,83). For a positive integer n, give each sampled prime the weight 1 plus its exponent in n and normalize by the sum of the five weights. These positive weights define a five-mode law to which the chart applies. This sampling includes a pseudocount at 83 and does not record the complete prime support of n.

For n = 5040 * 2^u * 3^v with u in {0,1,2} and v in {0,1}, put d = 13 + u + v. The five-mode law is (5+u,3+v,2,2,1)/d, its visible point is (4+v,3,2)/d, and its hidden coordinate is log((5+u)/(2*(3+v))). The six integer values are 5040, 10080, 15120, 20160, 30240 and 60480; their respective numerator vectors are (5,3,2,2,1), (6,3,2,2,1), (5,4,2,2,1), (7,3,2,2,1), (6,4,2,2,1) and (7,4,2,2,1). This finite application supplies neither an exhaustive congruence classification nor a Robin inequality for all integers above 5040.

**Theorem 1.1 (Global Fisher-orthogonal chart).**

Lean statement: `D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates.mixed_coordinates_global_chart`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates.mixed_coordinates_global_chart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathias Drton and Seth Sullivant (2007). *Algebraic Statistical Models*. DOI: [10.48550/arXiv.math/0703609](https://doi.org/10.48550/arXiv.math/0703609). URL: <https://arxiv.org/abs/math/0703609v1>.

*Commentary.*

Every positive law has its visible point in the open square pyramid 0 < X, Y, Z with X + Z < 1 and Y + Z < 1. Conversely, for every point of the open pyramid and every real c there is exactly one positive law with that visible point and chi = c. Along every direction u the derivative of chi at p equals the Fisher pairing of d with u, the base loop sums to zero, and it leaves X, Y and Z unchanged.

Fixing the visible point leaves one free parameter, the joint mass kappa = p_J, on the open interval from max(0, X + Y + Z - 1) to min(X, Y). With r = 1 - X - Y - Z, the condition chi = c is (r + kappa) kappa = e^c (X - kappa)(Y - kappa). The difference of the two sides is negative at the lower end and positive at the upper end, so the intermediate value theorem gives a root, and the difference is strictly increasing on the interval, so the root is unique. At c = 0 the root is kappa = XY / (1 - Z).

Because the Fisher pairing with d is the differential of chi, the fiber direction d is Fisher-orthogonal to every direction along which chi is constant. Log probability-ratio coordinates of positive categorical laws are classical in algebraic statistics and information geometry; the statement and proof here are for this five-mode simplex.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates.mixed_coordinates_global_chart`
