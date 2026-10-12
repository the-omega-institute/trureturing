# Mixed coordinates of the five-mode simplex

## Abstract

The three site occupancies and the log cross-ratio of the base corners form a global chart of the positive five-mode laws, and the base loop is the Fisher gradient of the cross-ratio.

A five-mode law is a probability vector p = (p_O, p_L, p_T, p_R, p_J) on the admissible words 000, 100, 010, 001, 101. Its visible point is (X, Y, Z) = (p_L + p_J, p_R + p_J, p_T), the occupancies of the first, last and middle sites. The hidden coordinate is chi = log(p_O p_J / (p_L p_R)), and the base loop is d = (1, -1, 0, -1, 1). The Fisher inner product at p is the sum over modes of u_s v_s / p_s.

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
