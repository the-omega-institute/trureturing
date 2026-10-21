# The Algebraic Coulter–Do Operator and Its Normalized Expansion

## Abstract

The ordered Coulter–Do differential operator has a partition basis, a nonzero normalization, detailed balance, and a normalized transposed coefficient expansion over RatFunc Complex.

The algebra is K[p_1,p_2,...], with weight(p_r)=r and positive r. Lean variable n represents p_(n+1). A partition rho represents the monomial p_rho with the actual part multiplicities as exponents. All natural weights are retained, including weight zero and the empty monomial. For a general characteristic-zero field and b in K, D_b is one half of the following three-term sum: (1+b) times the ordered sum of i*j*p_(i+j)*partial_i*partial_j; the ordered sum of (i+j)*p_i*p_j*partial_(i+j); and b times the sum of i*(i-1)*p_i*partial_i. Both double sums run over all positive ordered pairs. The operator is the linear extension of actual derivatives on every monomial. On the full homogeneous component of weight k its literal formula uses bound k; a derivative index exceeding that weight has zero monomial exponent. For a polynomial mixing weights, apply this argument to each of its finitely many monomials. This support observation describes the infinite operator, without a separate mixed-weight endpoint.

**Theorem 1.1 (All-Partition Expansion of a Homogeneous Polynomial).**

$$\forall K \in CommSemiring,\; \forall k \in Nat,\; \forall f \in \operatorname{PowerSum}\left(K\right),\; \operatorname{WeightedHomogeneous}\left(f, k\right) \Rightarrow f = \sum_{rho\in\operatorname{Partition}\left(k\right)}{{\operatorname{coeff}\left(f, rho\right)}\cdot{\operatorname{p}\left(rho\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2.homogeneous_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For this first statement K is any commutative semiring. The exponent-to-partition construction is inverse to the multiplicity map. Coefficient extraction and injectivity then give the expansion over every partition of k.

For the remaining statements fix K=RatFunc Complex, beta=X and alpha=1+X. Write B(rho,sigma) for the coefficient of p_sigma in D_beta(p_rho). Let m_r(rho) be the number of parts equal to r, z_rho the product of r^m_r(rho) times m_r(rho)! over the finite part support, and A_rho=alpha^(number of parts of rho)*z_rho.

**Theorem 1.2 (Every Partition Normalization Is Nonzero).**

$$\forall k \in Nat,\; \forall rho \in \operatorname{Partition}\left(k\right),\; \operatorname{A}\left(rho\right) \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2.normalization_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial 1+X has nonzero coefficient at degree one and stays nonzero in the rational function field. Each positive part power and factorial is positive, and its characteristic-zero image is nonzero. Positive part r is variable r-1, so its exponent is the multiplicity m_r. Reindexing the finite exponent product by r=i+1 gives product_r r^m_r*m_r!, including the empty product. This is source correspondence, with no separate normalization wrapper.

**Theorem 1.3 (Detailed Balance for Every Partition Pair).**

$$\forall k \in Nat,\; \forall lambda \in \operatorname{Partition}\left(k\right),\; \forall mu \in \operatorname{Partition}\left(k\right),\; {\operatorname{A}\left(lambda\right)}\cdot{\operatorname{B}\left(mu, lambda\right)} = {\operatorname{A}\left(mu\right)}\cdot{\operatorname{B}\left(lambda, mu\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2.operatorCoefficient_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal polynomial pairing has squared monomial norm alpha^length times z. Multiplication by p_i is adjoint to alpha*i*partial_i. Consequently each ordered join is adjoint to its ordered cut, and each Euler diagonal term is self-adjoint. This proves balance uniformly for equal parts, repeated parts, empty residuals, both transition directions, diagonal pairs and unrelated pairs.

**Theorem 1.4 (The Normalized Expansion in the Original Coefficient Orientation).**

$$\forall k \in Nat,\; \forall lambda \in \operatorname{Partition}\left(k\right),\; \sum_{mu\in\operatorname{Partition}\left(k\right)}{{\frac{\operatorname{B}\left(mu, lambda\right)}{\operatorname{A}\left(mu\right)}}\cdot{\operatorname{p}\left(mu\right)}} = \operatorname{D}\left({\frac{1}{\operatorname{A}\left(lambda\right)}}\cdot{\operatorname{p}\left(lambda\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2.normalized_operatorCoefficient_C2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Divide detailed balance by the two nonzero normalizations and use the partition expansion of the literal operator. The left coefficient is B(mu,lambda). The theorem holds at every natural weight, hence in particular at every positive weight. The companion occurrence source proves B(rho,sigma)=rowCoefficient beta rho sigma from erased occurrences, ordered cuts and the diagonal choose identity. It combines this with the canonical native C1 theorem and actual matching realization, giving a unique common coefficient function in the original conjecture.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2.homogeneous_expansion`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2.normalization_ne_zero`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2.normalized_operatorCoefficient_C2`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2.operatorCoefficient_balance`
