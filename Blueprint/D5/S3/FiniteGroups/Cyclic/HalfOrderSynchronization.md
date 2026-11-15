# Half-order failure in finite cyclic products

## Abstract

The actual half-order failure event in a nonempty finite family of cyclic groups has at most one part in two to the number of non-anchor coordinates.

Let I be a nonempty finite index type and let G(i) be finite cyclic groups, with possibly different sizes. Choose epsilon(i) of order two. Write P for the dependent product of the G(i), k for card(I), and B(G,epsilon) for the subtype of x in P satisfying NOT(Even(orderOf(x)) AND x^(orderOf(x)/2) unequal to epsilon). All group elements are included, in particular the identity and elements of odd order. The product P is not required to be cyclic.

**Theorem 1.1 (The all-family failure count).**

$$\forall I \in Typeu,\; [\operatorname{Fintype}\left(I\right)] [\operatorname{Nonempty}\left(I\right)] \forall G \in I \to Typev,\; [\forall i \in I,\; \operatorname{Group}\left(\operatorname{G}\left(i\right)\right)] [\forall i \in I,\; \operatorname{Fintype}\left(\operatorname{G}\left(i\right)\right)] [\forall i \in I,\; \operatorname{IsCyclic}\left(\operatorname{G}\left(i\right)\right)] \forall epsilon \in \operatorname{Pi}\left(I, G\right),\; \left(\forall i \in I,\; \operatorname{orderOf}\left(\operatorname{epsilon}\left(i\right)\right) = 2\right) \Rightarrow \operatorname{card}\left(\operatorname{B}\left(G, epsilon\right)\right) \cdot 2^{\operatorname{card}\left(I\right) - 1} \le \operatorname{card}\left(\operatorname{Pi}\left(I, G\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/HalfOrderSynchronization.failure_count_le` (`✓ std3`). ∎

*Citation.* Peter W. Shor (1997). *Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer*. DOI: [10.1137/S0097539795293172](https://doi.org/10.1137/S0097539795293172). URL: <https://arxiv.org/abs/quant-ph/9508027>.

*Commentary.*

In a cyclic factor epsilon is the unique element of order two. If d=orderOf(x) divides an even positive M, the local half-power x^(M/2) equals epsilon exactly when d.factorization(2)=M.factorization(2). Indeed its square is one; its being one is equivalent to d dividing M/2, or to 2*d dividing M, which is equivalent to strict inequality between the binary order valuations. For the product, Pi.orderOf and Finset.factorization_lcm express its binary order valuation as the maximum of the local valuations. Thus failure is exactly synchronization of every local valuation. If the product order is odd all the valuations are zero, so this case is retained.

Choose a full-order generator g(i) in each factor. Raising multiplication by g(i) to card(G(i))/2 multiplies the resulting half-power by epsilon(i), interchanging one and epsilon(i). The local half-power criterion therefore shows that multiplying any element by g(i) changes the binary valuation of its order. This argument applies to every even cyclic size and does not assign a finite binary valuation to the exponent zero.

Fix an anchor a in I. Encode a failing tuple x together with one Boolean b(i) for each i unequal to a by retaining x(a) and replacing x(i) by x(i)*g(i) exactly when b(i) is true. The anchor gives the common valuation t of the original tuple. In each other coordinate the encoded valuation equals t exactly when its bit is false, so equal encodings have equal bits. Cancellation of the generators then recovers the original tuples. This constructs an injection from B times the Boolean functions on I without a into the actual product P. The Boolean function type has cardinality 2^(k-1), giving the stated count. For k=1 there are no bits and every tuple fails; the inequality is equality.

The count is the classical common-valuation estimate of Shor, Section 5, PDF page 16. Its proof counts one fixed actual product, including heterogeneous cyclic sizes, rather than combining separately optimal fibers. It makes no assertion of mathematical novelty.

For odd N greater than one, put I=N.primeFactors and G(p)=(ZMod(p^(N.factorization(p)))) units. Every exponent is positive; each p is odd. ZMod.isCyclic_units_of_prime_pow supplies cyclicity, and the literal unit -1 has order two. The equivalence Units.mapEquiv((ZMod.equivPi N hN).toMulEquiv), followed by MulEquiv.piUnits, preserves order, natural powers, and literal -1. It therefore identifies the same literal Good(u) event, Even(orderOf(u)) and u^(orderOf(u)/2) unequal to -1, with the product event above. Its restriction is a bijection of failure subtypes, so Nat.card_congr transports the count without changing the uniform unit carrier.

Let T=card((ZMod N) units), F be its failure count, S its Good count, and q=2^(k-1). The transported estimate is F*q at most T. Since the unit carrier contains one, T is positive; q is positive, and S+F=T. Division in the real or rational numbers gives S/T at least 1-1/q. The pinned isPrimePow_iff_card_primeFactors_eq_one and nonemptiness of N.primeFactors imply k at least two when N is not a prime power. Then q is at least two and S/T is at least one half. All units, including one, are sampled uniformly; no independent latent probability law is assumed.

This establishes the classical unit-event count and its uniform normalization. It does not establish the simultaneous proper nontriviality of both gcd factors, or the bridge from unit half-powers to canonical representatives and original natural base powers. Those arithmetic bridges remain separate. No statement about hardware, complexity, quantum sampling, repeated-sample independence or full factoring completion follows from this count alone.

## References

- Truth anchor: `D5/S3/FiniteGroups/Cyclic/HalfOrderSynchronization.failure_count_le`
