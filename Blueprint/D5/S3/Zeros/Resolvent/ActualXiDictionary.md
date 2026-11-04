# The Actual Xi Analytic Dictionary

## Abstract

The actual xi analytic Taylor series, normal convergence, quantitative remainder and Hankel identity.

**Theorem 1.1 (The full actual xi analytic Taylor series).**

Lean statement: `D5/S3/Zeros/Resolvent/ActualXiDictionary.actual_xi_powerSeries`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Resolvent/ActualXiDictionary.actual_xi_powerSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The analytic owner uses the independently defined original xiOdd(w) = (i logDeriv xiReading(1/2-iw) - firstLiMass w)/(w squared + 1/4). Its spectral index is the positive-height subtype of the original canonical distinct-zero enumeration, with all actual analytic multiplicities. Positive height chooses exactly one representative of each reflection pair. The node is minus one divided by (rho minus one half) squared, and its weight is twice the actual multiplicity times the normalized rho(1-rho) reciprocal times the node.

The coordinate deductions give distinct nonzero nodes of norm less than one, nonzero weights, nonzero denominators, absolute weight summability, and finite node cuts away from zero. Reflection after conjugation restricts to an involution that conjugates nodes and weights and preserves multiplicity. A node is real exactly when the original zero is on the critical line; then node and weight are positive. Each off-line four-element zero orbit has precisely its two positive-height representatives, mapped injectively to one nonreal conjugate node pair. Multiplicity changes weights without duplicating the pair.

On norm(w) less than one quarter the original xi expression is analytic and equals the complete folded resolvent and the normally convergent odd series. The moment of every order j equals the original function derivative of order 2j+1 at zero divided by its factorial; every moment is real and all even derivatives vanish. W is the complete absolute weight mass and Lambda the actual supremum of node norms with zero included, with Lambda at most one. On every closed disk of radius r less than one quarter the bound is W r/(1-Lambda r squared), and the remainder after index J is bounded by W r (Lambda r squared) to power J+1 divided by the same denominator.

For every finite real coefficient vector u and natural shift m, the Hankel form built from the actual derivative coefficients at indices 2m+a+b equals the real part of the full sum of weight times [node to power m times p(node)] squared. This is the complex square, not a modulus square. Only an explicit Mathlib RiemannHypothesis premise gives nonnegativity. The dictionary proves no unconditional positivity, RH, physical-space moment condition, or negative-index formula. The folded pair count and the full odd/even Taylor-chain count remain distinct. The square-source, normalized-resolvent and actual endpoint-mass suppliers are reused in their canonical owners. No ordinary mathematical originality is claimed.

PositiveZero is the subtype of the original canonical distinct-zero enumeration whose imaginary part is positive. Reflection rho maps to 1-rho and selects exactly one sign of height; analytic multiplicity remains a positive natural weight. The complex node is gamma(rho) to the power minus two, equivalently minus one divided by (rho minus one half) squared. Its weight is twice the original multiplicity times the normalized reciprocal rho(1-rho) times that node. No off-line orbit is removed.

The restricted reflection-after-conjugation permutation is an involution and conjugates both node and weight, while preserving multiplicity. Equality of folded nodes forces equality or negation of gamma; positive height excludes negation, so distinct representatives give distinct nodes. Reality is equivalent to the original zero having real part one half. On those real nodes the node and weight are strictly positive. All nodes and weights are nonzero, the node norms lie strictly between zero and one, and the complete absolute weight sum converges.

For every positive epsilon the indices with node norm at least epsilon form a finite set, by the actual zero source spectral-ball finiteness. This is about distinct zeros, not occurrence fibers: multiplicity changes the weights without multiplying the number of off-line conjugate node pairs. These are classical coordinate and convergence facts; no ordinary originality or Riemann-hypothesis conclusion is asserted.

The independent function xiOdd(w) is (i times logDeriv xiReading at one half minus i w, minus the original real firstLiMass times w), divided by w squared plus one quarter. It is defined directly from the existing xiReading and is never defined by a spectral series.

The positive-height square-resolvent HasSum supplier and the original complex endpoint-mass HasSum are reused with the canonical actualData. Reflection folds the mass to twice each positive-height contribution. Subtracting these two convergent sums first, and then dividing by the common denominator, gives the exact summand w times weight divided by one minus node times w squared. No divergent reciprocal-zero sums are split.

The HasSum identity holds for every complex w with norm less than one quarter, including zero. The entire square-source logDeriv composition and xi reflection pay the center without dividing by w. The actual height exclusion proves the required xi nonvanishing on this disk; it is not an added convergence or zero-free hypothesis. Off-line zeros and all analytic multiplicities remain present.

The complex moment of order j is the complete sum of weight times node to power j over actual positive-height zero indices. Absolute weight summability and the bounded complex nodes justify every moment and the double geometric series. Its sum on norm(w) less than one quarter is the independently defined xiOdd(w).

The full scalar formal power series has zero even coefficients and moment j at coefficient 2j+1. The kernel-checked formal-power-series factorial identity identifies moment j with iteratedDeriv(2j+1, xiOdd)(0) divided by (2j+1) factorial, at every natural j. All even iterated derivatives vanish. The same full series proves analyticity throughout the disk. Conjugation of actual indices makes every moment real.

Let W be the complete sum of absolute weights and Lambda the supremum of the node norms with zero included. Lambda lies between zero and one. The moment norm is at most W times Lambda to power j. The coefficients are analytic data of the genuine xi expression; the moment interpretation is a proved identity, not a replacement definition of xi or its logarithmic derivative.

Keep the same actual xi function, nodes, weights, moments, total absolute mass W, and node-norm supremum Lambda. For every nonnegative r less than one quarter, the folded resolvent and its odd Taylor series both have summable uniform majorants on the closed disk of radius r.

The xi function is bounded there by W r divided by (1 minus Lambda r squared). After retaining the odd moment terms through index J, its remainder is at most W r times (Lambda r squared) to power J+1, divided by (1 minus Lambda r squared). The finite sum has exactly J+1 odd terms, and the complete infinite tail is retained in the proof.

The bounds follow from the complex denominator reverse triangle inequality, moment estimates, and a genuinely summable geometric tail. No tail truncation is substituted for the original function, and neither positivity nor RH is used.

For each natural j define xiCoefficient(j) as the real part of iteratedDeriv(2j+1, xiOdd)(0) divided by (2j+1) factorial. The preceding all-order dictionary identifies it with the real actual folded moment. For arbitrary natural N and m and real coefficients indexed by Fin(N+1), put p(z) equal to their finite power polynomial.

The finite Hankel form sum over a,b of u(a) u(b) xiCoefficient(2m+a+b) equals the real part of the complete sum over actual positive-height zeros of weight times the complex square of node to power m times p(node). Finite distributivity and summable moment columns justify the equality and absolute convergence. The square is the complex algebraic square; it is never a squared norm.

With Mathlib RiemannHypothesis explicitly assumed, every node and weight is positive real, so this same finite form is nonnegative. There is no unconditional positivity or RH theorem. An off-line quadruple folds to one nonreal conjugate pair of distinct nodes; analytic multiplicity changes weights, not pair counts. No folded or full-chain negative-index count is proved here. A spectral power factor imposes no physical-space atom moment condition.

The coordinate identities are deductions from the retained definitions and suppliers, rather than additional named normalization corollaries. Since gamma=(rho-1/2)/i, gamma squared is minus (rho-1/2) squared, so node=-1/(rho-1/2) squared. The retained gamma norm bound and node_norm give 0<norm(node)<1. The weight_node formula, positive analytic multiplicity, nonzero gamma and node_denominator_ne_zero give a nonzero weight. For epsilon>0, epsilon<=norm(node) implies norm(gamma) squared<=1/epsilon, hence norm(gamma)<=1/epsilon+1; actualData.locallyFinite and injectivity of subtype inclusion make that node cut finite.

The reflection section follows by the nonzero imaginary part of every actual zero: a positive-height index represents itself, and a negative-height index is represented by its reflection. Reflection reverses height and is involutive, proving uniqueness. For an off-line positive-height zero, conjugation cannot fix its nonzero height; zero_orbit_card_four_of_off_line gives four distinct orbit indices. Reflection and ordinary conjugation have negative height, leaving exactly n and reflection(conjugation(n)) in PositiveZero. The commuting symmetries identify the latter with conjugation(reflection(n)). node_injective and node_real_iff identify their nodes as exactly one distinct nonreal conjugate pair. Multiplicities are preserved by both source symmetries.

The scalar resolvent is the same complete convergent identity with w outside the sum: for nonzero w, divide actual_xi_folded_hasSum by w to obtain the summable scalar terms and then multiply their sum by w. At w=0 the terms reduce to weight, which is absolutely summable, while xiOdd_square gives xiOdd(0)=0. No convergence assumption is introduced at the center.

Parity and analyticity require no extra retained aliases. The consumed moment_real proof conjugates the absolutely convergent moment sum and reindexing by the involutive PositiveZero conjugation, using weight_conjugation and node_conjugation, to obtain conj(moment(j))=moment(j), hence imaginary part zero. It is used by the exact complex coefficient reconstruction in xiCoefficient_eq, which is consumed by the Hankel identity. actual_xi_coefficient_derivative identifies every coefficient with the original xi derivative divided by its factorial. coefficient(2j)=0 by its definition, and the factorial is nonzero, so all even derivatives vanish. actual_xi_powerSeries gives analyticity at every point of the open disk.

The non-normalization analytic step is the complete double-series estimate and exchange in double_summable and actual_xi_moment_hasSum, used by actual_xi_powerSeries and all derivative identities. The quantitative owner also proves the uniform denominator majorant and shifted infinite geometric remainder. Spectrum and resolvent transformations are consumed suppliers inside this owner; they are not independently described first-freeze modules. New source-family escape audits remain unfinished under https://github.com/the-omega-institute/trureturing/issues/26172. That linked issue supplies neither mathematical admission nor declared_validated evidence.

**Theorem 1.2 (The complete geometric remainder).**

Lean statement: `D5/S3/Zeros/Resolvent/ActualXiDictionary.actual_xi_taylor_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Resolvent/ActualXiDictionary.actual_xi_taylor_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement uses the same independently defined xi function and complete actual-zero source described above.

**Theorem 1.3 (Every finite real polynomial and shift).**

Lean statement: `D5/S3/Zeros/Resolvent/ActualXiDictionary.actual_xi_hankel_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Resolvent/ActualXiDictionary.actual_xi_hankel_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement uses the same independently defined xi function and complete actual-zero source described above.

## References

- Truth anchor: `D5/S3/Zeros/Resolvent/ActualXiDictionary.actual_xi_hankel_identity`
- Truth anchor: `D5/S3/Zeros/Resolvent/ActualXiDictionary.actual_xi_powerSeries`
- Truth anchor: `D5/S3/Zeros/Resolvent/ActualXiDictionary.actual_xi_taylor_remainder`
- Dependency: [D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds](../../Weil/ZeroData/ActualReciprocalSquareBounds.md)
