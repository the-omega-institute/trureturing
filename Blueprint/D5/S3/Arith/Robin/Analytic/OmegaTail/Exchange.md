# Paired prime exchanges

## Abstract

Signed prime exchanges on a fixed base and counting on an exponential grid.

**Definition 1.1 (Integers from paired choices).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.pairedOutputs`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.pairedOutputs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In each bin take all donor and recipient subsets of the prescribed sizes. For each tuple of choices, remove the union of the donor subsets from the base, add the union of the recipient subsets, and multiply the elements of the resulting support. The output family is the image of the entire finite product of choices under this map.

**Theorem 1.2 (Exact size and pointwise logarithmic budget).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.paired_exchange`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.paired_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the donor bins be pairwise disjoint subsets of a finite prime base. Let the recipient bins consist of primes outside the base and be pairwise disjoint. In each paired bin choose h(i) donors and independently choose h(i) recipients. The lower donor log bound is lo(i) and the upper recipient log bound is hi(i). Suppose the base log sum plus the sum of h(i) times the difference hi(i) minus lo(i) is strictly below log(x), for x positive.

The product of the resulting prime support is positive, squarefree, below x, and has exactly as many distinct prime factors as the base. The donor choice is the part of its bin missing from the support. The recipient choice is the intersection of its bin with the support. The Lower lemmas recover the prime support from the product, recover each bin choice, and identify the number of distinct factors with the support cardinality. Therefore the number of outputs equals the product over bins of both binomial coefficients. The statement allows an empty index type, zero choices, and choices filling a bin.

**Theorem 1.3 (Finite count on the exponential grid).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.fixed_grid_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.fixed_grid_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a strictly increasing grid t starting at zero and positive real parameters P and s. Bin i consists of primes in the half-open interval from P exp(-t(i+1)/s) to P exp(-t(i)/s) on the donor side, and from P exp(t(i)/s) to P exp(t(i+1)/s) on the recipient side. Assume the base consists of primes up to P, contains the donor bins, and has size above the threshold at exp(P) for lambda. Its logarithmic cost is at most P minus the reserve, and the exchange cost bound (2/s) times the sum of t(i+1) h(i) is strictly below the reserve.

The signed exchange gives a lower bound on the literal distinct-prime tail at exp(P), equal to the product of the two binomial coefficients for each bin. The exponential endpoints provide the donor lower and recipient upper log bounds, and the common log(P) cancels within each pair.

**Theorem 1.4 (Actual fixed-grid family and its entropy).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.fixed_grid_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.fixed_grid_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the grid above with interior densities q(i), positive eta, c = pi/(2 sqrt(3)), C = (1+eta)c, s = C sqrt(log(P)), W = (P/log(P))/s, and Z = (P/log(P))/sqrt(log(P)). Let delta(i) be the width of bin i. Twice the sum of t(i+1) delta(i) q(i) must be less than (pi^2/6)(1+eta)^2.

The quantitative prime-counting expansion gives both moving bin sizes asymptotic to W times delta(i). Delete exactly primeCount(P) minus k(P) primes from the interval (P/2, 3P/4], where k(P) is floor(T_2(exp(P)))+1. The far deletion theorem supplies a deletion of that size and gives every such retained base size k(P) and log sum at most P minus the safe reserve. The window lies eventually below every donor bin, so all donors survive. The centered reserve theorem gives the limit 2 after normalizing the safe reserve by P/log(P)^2. Normalizing by W/s gives the limit (pi^2/6)(1+eta)^2.

Take h(i) to be the floor of q(i) times the smaller of the two bin sizes. Its ratio to W tends to delta(i) q(i). The floor fits in both bins. Strict normalized slack makes the exchange feasible for all sufficiently large P. The image of all the paired choices is nonempty and has cardinality equal to the full product of both binomial coefficients over the grid. Each integer in that image is positive, squarefree, strictly below exp(P), and has exactly k(P) distinct prime factors.

The two log binomial coefficients in each bin contribute 2 delta(i) H(q(i)) on scale W, with H the binary entropy. For each positive zeta, the log cardinality of the constructed family is eventually at least Z times (2 sum(delta(i) H(q(i)))/C minus zeta). Since k(P) is strictly above the true second threshold, the same lower bound holds for the log of the second-threshold tail count.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.fixed_grid_bound`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.fixed_grid_lower`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.pairedOutputs`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange.paired_exchange`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Entropy](Entropy.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion](FarDeletion.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Lower](Lower.md)
