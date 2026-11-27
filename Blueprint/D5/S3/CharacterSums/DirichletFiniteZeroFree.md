# An actual L-function criterion with horizontal margin

## Abstract

Finite arithmetic tests for Dirichlet zero exclusion

Let χ be a primitive nonprincipal complex Dirichlet character of positive modulus q. Fix real C and T, a positive real ε, and a natural arithmetic cutoff X. The moments are the negative real parts of the normalized von Mangoldt sums on the line Re s = 2.

**Definition 1.1 (The starting exponent).**

$$\operatorname{momentStart}\left(B, C, r\right) = \operatorname{add}\left(2, \operatorname{ceilingNat}\left(\operatorname{max}\left(\operatorname{ratio}\left(\operatorname{realLog}\left(\operatorname{mul}\left(16, B\right)\right), \operatorname{realLog}\left(\operatorname{ratio}\left(4, 3\right)\right)\right), \operatorname{ratio}\left(\operatorname{realLog}\left(\operatorname{mul}\left(6, \operatorname{add}\left(C, 2\right)\right)\right), \operatorname{realLog}\left(\operatorname{ratio}\left(\operatorname{ratio}\left(3, 2\right), r\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/CharacterSums/DirichletFiniteZeroFree.momentStart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write M = momentStart(B,C,r). The first threshold controls the far spectrum; the second controls amplification. M is always at least two. The real logarithm is total, and all ceilings are natural ceilings.

**Definition 1.2 (The last tested order).**

$$\operatorname{momentOrder}\left(B, C, r\right) = \operatorname{sub}\left(\operatorname{mul}\left(\operatorname{momentStart}\left(B, C, r\right), \operatorname{power}\left(6, \operatorname{ceilingNat}\left(\operatorname{mul}\left(4, B\right)\right)\right)\right), 1\right)$$

*Formalization.* `D5/S3/CharacterSums/DirichletFiniteZeroFree.momentOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write K = M 6^ceil(4B) - 1, using natural subtraction.

**Definition 1.3 (The number of grid intervals).**

$$\operatorname{gridSize}\left(T, eps\right) = \operatorname{max}\left(1, \operatorname{ceilingNat}\left(\operatorname{ratio}\left(\operatorname{mul}\left(2, T\right), eps\right)\right)\right)$$

*Formalization.* `D5/S3/CharacterSums/DirichletFiniteZeroFree.gridSize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

J = max(1,ceil(2T/ε)); the height grid has J+1 points.

**Definition 1.4 (The grid height).**

$$\operatorname{gridPoint}\left(T, eps, j\right) = \operatorname{add}\left(\operatorname{neg}\left(T\right), \operatorname{ratio}\left(\operatorname{mul}\left(\operatorname{mul}\left(2, T\right), j\right), \operatorname{gridSize}\left(T, eps\right)\right)\right)$$

*Formalization.* `D5/S3/CharacterSums/DirichletFiniteZeroFree.gridPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

t(j) = -T+2Tj/J. The tests use 0 ≤ j ≤ J, including both endpoints.

For any square-summable complex spectrum z with square mass at most B and 0 < r < 3/2, it suffices to bound the power moments Re(sum z(i)^(k+1)) by (C+1)(2/3)^k only when M-1 ≤ k ≤ K and M divides k+1. Every spectral norm is then strictly less than 1/r. The indices with norm greater than 1/2 form a finite set of size at most ceil(4B). Simultaneous circle approximation aligns their phases at n = Mu with 1 ≤ u ≤ 6^ceil(4B). The complementary norm is at most B(1/2)^(n-2). Put D = (C+1)(3/2) and A = ((3/2)/r)^n > 1. A norm at least 1/r forces A/2 ≤ D+1/4 ≤ A/4+1/4, a contradiction.

The grid argument needs Re ρ ≤ 1 only for a member already satisfying Re ρ ≥ 1/2+ε and |Im ρ| ≤ T. All other members need only the square budgets and sparse moments at the grid centers. The starting radius and square summability remain essential: at r = 3/2 the amplification logarithm vanishes, while a divergent series has a totalized tsum that need not express its mass.

**Definition 1.5 (The inverse-square budget).**

$$\operatorname{zeroBudget}\left(q, T\right) = \operatorname{add}\left(\operatorname{realLog}\left(\operatorname{mul}\left(q, \operatorname{add}\left(T, 3\right)\right)\right), 4\right)$$

*Formalization.* `D5/S3/CharacterSums/DirichletFiniteZeroFree.zeroBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write B = log(q(T+3))+4. For nonnegative T this bounds the sum of squared inverse distances over all zeros, with multiplicity.

**Definition 1.6 (The finite order limit).**

$$\operatorname{zeroOrder}\left(q, C, T, eps\right) = \operatorname{momentOrder}\left(\operatorname{zeroBudget}\left(q, T\right), C, \operatorname{sub}\left(\operatorname{ratio}\left(3, 2\right), \operatorname{ratio}\left(eps, 2\right)\right)\right)$$

*Formalization.* `D5/S3/CharacterSums/DirichletFiniteZeroFree.zeroOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Put r = 3/2 - ε/2, M = 2 + ceil(max(log(16B)/log(4/3), log(6(C+2))/log((3/2)/r))), and K = M 6^ceil(4B) - 1. Each ceiling is the natural ceiling. This is the same momentOrder used by the finite spectral exclusion theorem.

**Theorem 1.7 (The finite arithmetic criterion).**

$$\forall q \in \operatorname{PositiveNaturals}\left(\right),\; \forall chi \in \operatorname{ComplexDirichletCharacters}\left(q\right),\; \forall C \in \operatorname{Reals}\left(\right),\; \forall T \in \operatorname{Reals}\left(\right),\; \forall eps \in \operatorname{PositiveReals}\left(\right),\; \forall X \in \operatorname{Naturals}\left(\right),\; \operatorname{implies}\left(\operatorname{and}\left(\operatorname{primitiveNonprincipal}\left(chi\right), \operatorname{and}\left(\operatorname{le}\left(\operatorname{exp}\left(\operatorname{mul}\left(4, \operatorname{add}\left(\operatorname{zeroOrder}\left(q, C, T, eps\right), 1\right)\right)\right), X\right), \forall j \in \operatorname{Naturals}\left(\right),\; \operatorname{implies}\left(\operatorname{le}\left(j, \operatorname{gridSize}\left(T, eps\right)\right), \forall k \in \operatorname{Naturals}\left(\right),\; \operatorname{implies}\left(\operatorname{and}\left(\operatorname{le}\left(\operatorname{sub}\left(\operatorname{momentStart}\left(\operatorname{zeroBudget}\left(q, T\right), C, \operatorname{sub}\left(\operatorname{ratio}\left(3, 2\right), \operatorname{ratio}\left(eps, 2\right)\right)\right), 1\right), k\right), \operatorname{and}\left(\operatorname{le}\left(k, \operatorname{zeroOrder}\left(q, C, T, eps\right)\right), \operatorname{divides}\left(\operatorname{momentStart}\left(\operatorname{zeroBudget}\left(q, T\right), C, \operatorname{sub}\left(\operatorname{ratio}\left(3, 2\right), \operatorname{ratio}\left(eps, 2\right)\right)\right), \operatorname{add}\left(k, 1\right)\right)\right)\right), \operatorname{le}\left(\operatorname{finiteMoment}\left(chi, k, X, \operatorname{gridPoint}\left(T, eps, j\right)\right), \operatorname{mul}\left(\operatorname{add}\left(C, \operatorname{ratio}\left(1, 3\right)\right), \operatorname{power}\left(\operatorname{ratio}\left(2, 3\right), k\right)\right)\right)\right)\right)\right)\right), \operatorname{and}\left(\operatorname{closedRectangleZeroFree}\left(chi, \operatorname{add}\left(\operatorname{ratio}\left(1, 2\right), eps\right), T\right), \operatorname{implies}\left(\operatorname{le}\left(0, T\right), \forall j \in \operatorname{Naturals}\left(\right),\; \operatorname{implies}\left(\operatorname{le}\left(j, \operatorname{gridSize}\left(T, eps\right)\right), \operatorname{closedDiskZeroFree}\left(chi, \operatorname{add}\left(2, \operatorname{mul}\left(\operatorname{gridPoint}\left(T, eps, j\right), \operatorname{imaginaryUnit}\left(\right)\right)\right), \operatorname{sub}\left(\operatorname{ratio}\left(3, 2\right), \operatorname{ratio}\left(eps, 2\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletFiniteZeroFree.finite_moment_zero_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J = max(1,ceil(2T/ε)) and t(j) = -T + 2Tj/J for 0 ≤ j ≤ J. Suppose X ≥ exp(4(K+1)) and, for all those j and M-1 ≤ k ≤ K with M dividing k+1, finiteMoment(χ,k,X,t(j)) ≤ (C+1/3)(2/3)^k. Then L(s,χ) ≠ 0 whenever Re s ≥ 1/2+ε and |Im s| ≤ T, including the rectangle boundary. If T ≥ 0, it also excludes every closed disk |s-(2+i t(j))| ≤ 3/2-ε/2, for 0 ≤ j ≤ J. The theorem allows any real C and T. A negative T gives an empty rectangle. If ε > 1/2 the usual nonvanishing to the right of one already suffices.

Repeat each actual zero according to its positive analytic order. Absolute convergence transports the weighted power sums and the inverse-square budget to this repeated family. The finite arithmetic tail has magnitude at most (2/3)^(k+1), so a tested coefficient C+1/3 gives C+1 for the full moments. The grid remains inside the height interval, and the finite spectral theorem gives inverse distances strictly below 1/r, which excludes each closed grid disk of radius r when 0 < r < 3/2. At ε = 3 the disk is its nonzero center of real part two; at ε > 3 its radius is negative and the disk is empty. The rectangle is excluded by the same detector and grid geometry. Entire nonzero L-functions have positive finite order at every zero, so this excludes actual zeros, not just an auxiliary list.

For a prime p, every nonprincipal character modulo p is primitive: its conductor divides p, and conductor one would make it principal. Set T = 4√p, B = log(p(4√p+3))+4, J = max(1,ceil(8√p/ε)), K = momentOrder(B,C,3/2-ε/2), and X ≥ exp(4(K+1)). The stated finite inequalities then exclude all zeros with Re s ≥ 1/2+ε and |Im s| ≤ 4√p. This applies in particular to nonprincipal characters whose order divides rad(p-1); no character-order assumption is needed.

The exact finite-height premise used for problem 985 asks for Re s > 1/2 at this height. One fixed positive ε leaves a strip untreated. To obtain that premise by this criterion, the finite tests must be supplied for every positive ε, or for a sequence tending to zero. C and X may vary with ε. The criterion proves no unconditional arithmetic moment inequalities and does not establish that remaining supply.

## References

- Truth anchor: `D5/S3/CharacterSums/DirichletFiniteZeroFree.finite_moment_zero_free`
- Truth anchor: `D5/S3/CharacterSums/DirichletFiniteZeroFree.gridPoint`
- Truth anchor: `D5/S3/CharacterSums/DirichletFiniteZeroFree.gridSize`
- Truth anchor: `D5/S3/CharacterSums/DirichletFiniteZeroFree.momentOrder`
- Truth anchor: `D5/S3/CharacterSums/DirichletFiniteZeroFree.momentStart`
- Truth anchor: `D5/S3/CharacterSums/DirichletFiniteZeroFree.zeroBudget`
- Truth anchor: `D5/S3/CharacterSums/DirichletFiniteZeroFree.zeroOrder`
- Dependency: [D5/S3/CharacterSums/DirichletZeroBounds](DirichletZeroBounds.md)
- Dependency: [D5/S3/CharacterSums/DirichletZeroPowerSums](DirichletZeroPowerSums.md)
