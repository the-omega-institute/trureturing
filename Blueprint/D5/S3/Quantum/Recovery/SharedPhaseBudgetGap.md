# SharedPhaseBudgetGap

## Abstract

A uniform strict improvement of the four-record phase-cone recovery bound.

**Theorem 1.1 (Strict shared-phase budget gap).**

Lean statement: `D5/S3/Quantum/Recovery/SharedPhaseBudgetGap.first_hop_original`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/SharedPhaseBudgetGap.first_hop_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let s be the positive square root of two, let nu = 3 - 2s, and let B have rows (-1/s, -1/s, 1, 0) and (-1/s, -i/s, 0, 1). Let M = B B star. For a finite family of phase vectors z_j in the four-dimensional complex torus and nonnegative real weights p_j, assume the residual M minus the weighted sum of the rank-one matrices (B z_j)(B z_j) star is positive semidefinite.

There is a positive real gamma, independent of the finite family, such that the total weight is at most 4/nu - gamma. The proof identifies every equality phase as one of two explicit one-parameter families, computes M as the matrix with diagonal entries 2 and off-diagonal entries (1-i)/2 and (1+i)/2, and uses compactness together with a shared non-diagonal perturbation to obtain a uniform strict separation.

The quantified family allows any positive finite index type; the underlying phase-cone estimate also applies to the empty family. The statement concerns the compressed shared budget and does not assert an operational realization theorem or a sharp small-noise asymptotic.

**Theorem 1.2 (Strict improvement for the noisy phase cone).**

Lean statement: `D5/S3/Quantum/Recovery/SharedPhaseBudgetGap.eta_strict_improvement`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/SharedPhaseBudgetGap.eta_strict_improvement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R0 have rows (1,0), (0,1), (1/s,1/s), and (1/s,i/s), put C0 = R0 R0 star, and define C_epsilon = (1-epsilon) C0 + epsilon I4. For a matrix C, eta(C) is the supremum of the total nonnegative weights of all finite phase families whose weighted rank-one sum is bounded above by C in the positive semidefinite order. A one-branch family with zero weight represents the empty decomposition.

There is one gamma > 0 such that, for every epsilon in [0,1], eta(C_epsilon) is at most (4/nu - gamma) epsilon. The feasible masses contain zero, are bounded above, and have eta(C_epsilon) as their least upper bound. Thus this is a strict coefficient improvement over 4 epsilon/nu for every positive epsilon.

The bridge uses B R0 = 0 and B C_epsilon B star = epsilon M. Congruence by B sends each actual feasible phase decomposition to the same compressed family. For positive epsilon, dividing its weights by epsilon applies the common budget gap. At epsilon = 0, nonnegative weights and the positive phase-energy lower bound force total mass zero. Taking the supremum preserves the uniform bound.

This upper bound does not determine the optimal compressed constant K, its attainment or algebraic value, or the sharp first-order limit of eta(C_epsilon)/epsilon. Those questions remain open. The finite-POVM realization equivalence is not established here, so the result is stated for the phase-cone quantity without an operational claim.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/SharedPhaseBudgetGap.eta_strict_improvement`
- Truth anchor: `D5/S3/Quantum/Recovery/SharedPhaseBudgetGap.first_hop_original`
