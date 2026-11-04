# Replica order four for the (m, 1, 1) Gaussian state

## Abstract

At replica order four the sixteen Fourier modes of the replica torus collapse the tripartite product of the fully symmetric pure Gaussian state into the three cut products and three squared factors. For party sizes (m, 1, 1) this gives an exact closed form of the genuine multi-entropy, its constant, its first correction and a uniform bound for the remainder.

**Theorem 1.1 (The order-four product identity).**

$$P_{3}=P_{A}P_{B}P_{C}\prod_{v}(1+\frac{x(s+v)}{2})^2$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour.tripartiteProduct_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative real A, B, C with nonzero sum and every real x, the order-four tripartite product equals the product of the three cut products with coefficients A(B + C), B(A + C), C(A + B) and of the squares of 1 + x(s + v)/2 for v in {AB, AC, BC}, where s = AB + AC + BC. At n = 4 the root of unity is i, and the sixteen sine weights take the values 0, u_i/2, u_i and (s + v)/2.

**Theorem 1.2 (The closed form for (m, 1, 1)).**

$$GM_{4}=\frac{1}{24}\log \frac{((3m+1)a^2-m+1)^4}{(m+1)(m a^2+1)^2(2m a^2-m+1)(a^2+1)^4}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour.GM3_four_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer m >= 1 and every real a >= 1, the genuine multi-entropy at replica order four of the fully symmetric pure Gaussian state with party sizes (m, 1, 1) is one twenty-fourth of the logarithm of the displayed rational function of a^2. With x = (a^2 - 1)/(m + 1), every factor of the order-four product identity is an explicit rational function of a^2, and the Fourier product formula gives the logarithm.

**Definition 1.3 (The replica-four constant).**

$$K_{4}(m)=\frac{1}{24}\log \frac{(3m+1)^4}{2m^3(m+1)}$$

*Formalization.* `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour.K4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constant term of the large-squeezing expansion at replica order four for party sizes (m, 1, 1).

**Definition 1.4 (The first correction).**

$$c_{4}(m)=-\frac{29m^2+14m+5}{48m(3m+1)}$$

*Formalization.* `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour.c4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient of a^(-2) in the large-squeezing expansion at replica order four for party sizes (m, 1, 1).

**Theorem 1.5 (The expansion with a uniform remainder bound).**

$$0\leq GM_{4}-(-\frac{\log a}{4}+K_{4}(m)+\frac{c_{4}(m)}{a^2})\leq\frac{1}{8a^4}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour.GM3_four_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer m >= 1 and every real a >= 1, the remainder R_4 = GM_4 - (-(log a)/4 + K_4(m) + c_4(m)/a^2) satisfies 0 <= R_4 <= 1/(8a^4). With t = 1/a^2, r = (m - 1)/(3m + 1), b = 1/m and s_0 = (m - 1)/(2m), the closed form gives GM_4 = -(log a)/4 + K_4(m) + h(t)/24 with h(t) = 4 log(1 - rt) - 2 log(1 + bt) - log(1 - s_0 t) - 4 log(1 + t). On [0, 1] the second derivative of h lies between 0 and 6, and two monotonicity arguments for h(t) - h'(0) t and 3t^2 - (h(t) - h'(0) t) give the bounds; h'(0)/24 = c_4(m).

**Theorem 1.6 (The replica-four limit).**

$$\lim_{a\to\infty}(GM_{4}+\frac{1}{4}\log a)=K_{4}(m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour.GM3_four_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer m >= 1, the genuine multi-entropy at replica order four plus (log a)/4 tends to K_4(m) as a tends to positive infinity. The remainder bound squeezes the difference between K_4(m) + c_4(m)/a^2 and K_4(m) + c_4(m)/a^2 + 1/(8a^4).

**Theorem 1.7 (The residual-determinant constant at order four).**

$$K_{4}(m,1,1)=K_{4}(m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour.residualConstant_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer m >= 1, the residual-determinant constant of replica order four for party sizes (m, 1, 1) equals K_4(m). Both the residual-determinant limit and the replica-four limit describe the limit of the same function, and limits are unique.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour.GM3_four_closed`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour.GM3_four_remainder`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour.GM3_four_tendsto`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour.K4`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour.c4`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour.residualConstant_four`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour.tripartiteProduct_four`
- Dependency: [D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit](ResidualLimit.md)
