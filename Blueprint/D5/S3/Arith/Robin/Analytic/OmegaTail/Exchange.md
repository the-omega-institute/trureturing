# Paired prime exchanges

## Abstract

Signed prime exchanges on a fixed base and counting on an exponential grid.

**Theorem 1.1 (Exact size and pointwise logarithmic budget).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.paired_exchange`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.paired_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the donor bins be pairwise disjoint subsets of a finite prime base. Let the recipient bins consist of primes outside the base and be pairwise disjoint. In each paired bin choose h(i) donors and independently choose h(i) recipients. The lower donor log bound is lo(i) and the upper recipient log bound is hi(i). Suppose the base log sum plus the sum of h(i) times hi(i) minus lo(i) is strictly below log(x), for x positive.

The product of the resulting prime support is positive, squarefree, below x, and has exactly as many distinct prime factors as the base. The donor choice is the part of its bin missing from the support. The recipient choice is the intersection of its bin with the support. Prime factorization recovers the support, so the number of outputs equals the product over bins of both binomial coefficients. The statement allows an empty index type, zero choices, and choices filling a bin.

**Theorem 1.2 (Finite count on the exponential grid).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.fixed_grid_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.fixed_grid_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a strictly increasing grid t starting at zero and positive real parameters P and s. Bin i consists of primes in the half-open interval from P exp(-t(i+1)/s) to P exp(-t(i)/s) on the donor side, and from P exp(t(i)/s) to P exp(t(i+1)/s) on the recipient side. Assume the base consists of primes up to P, contains the donor bins, and has size above the threshold at exp(P) for lambda. Its logarithmic cost is at most P minus the reserve, and the exchange cost bound (2/s) times the sum of t(i+1) h(i) is strictly below the reserve.

The signed exchange gives a lower bound on the literal distinct-prime tail at exp(P), equal to the product of the two binomial coefficients for each bin. The exponential endpoints provide the donor lower and recipient upper log bounds, and the common log(P) cancels within each pair.

**Theorem 1.3 (Entropy bound from moving capacities and a safe base).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.fixed_grid_lower_of_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.fixed_grid_lower_of_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the grid above with interior densities q(i), positive eta, c = pi/(2 sqrt(3)), C = (1+eta)c, s = C sqrt(log(P)), W = (P/log(P))/s, and Z = (P/log(P))/sqrt(log(P)). Let delta(i) be the width of bin i. Twice the sum of t(i+1) delta(i) q(i) must be less than (pi^2/6)(1+eta)^2.

Assume both bin sizes divided by W converge to delta(i), and the supplied reserve divided by W/s converges to (pi^2/6)(1+eta)^2. For all sufficiently large P, the supplied base consists of primes up to P, contains every donor bin, has exactly floor(T_2(exp(P)))+1 elements, and has log sum at most P minus the reserve. In Lemma 7.6 the reserve is D_safe from Lemma 7.3 and the base is its retained prime set.

Take h(i) to be the floor of q(i) times the smaller of the two bin sizes. Its ratio to W tends to delta(i) q(i). The finite grid bound applies eventually by strict normalized slack. The two log binomial coefficients in each bin contribute 2 delta(i) H(q(i)) on scale W, with H the binary entropy. For each positive zeta, the log of the second-threshold count at exp(P) is eventually at least Z times the coefficient 2 sum(delta(i) H(q(i)))/C minus zeta, with the subtraction inside the coefficient.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.fixed_grid_bound`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.fixed_grid_lower_of_capacity`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.paired_exchange`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Entropy](Entropy.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Selection](Selection.md)
