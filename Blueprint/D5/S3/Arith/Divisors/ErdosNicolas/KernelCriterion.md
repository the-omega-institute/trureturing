# The strict two-block kernel criterion

## Abstract

The strict two-block kernel criterion

**Theorem 1.1 (The block criterion).**

$$\forall a \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall A \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall B \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall p \in \mathbb{Q},\; \forall bA \in \mathbb{Q},\; \forall bB \in \mathbb{Q},\; \forall F \in \mathbb{Q},\; 0 < L \Rightarrow \left(\operatorname{Disjoint}\left(A, B\right) \Rightarrow \left(0 < \operatorname{card}\left(A\right) \Rightarrow \left(\operatorname{card}\left(B\right) \le a \cdot \operatorname{card}\left(A\right) \Rightarrow \left(\operatorname{pairSum}\left(A\right) \le bA \cdot \operatorname{card}\left(A\right) \Rightarrow \left(\operatorname{pairSum}\left(B\right) \le \frac{bB \cdot a \cdot \operatorname{card}\left(A\right)}{p} \Rightarrow \left(\operatorname{crossResidual}\left(L, A, B\right) \le F \cdot \operatorname{card}\left(A\right) \Rightarrow \left(\operatorname{KernelTest}\left(a, p, L, bA, bB, F\right) \Rightarrow \operatorname{pairSum}\left(\operatorname{union}\left(A, B\right)\right) < \left(a + 1\right) \cdot \operatorname{card}\left(A\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ErdosNicolas/KernelCriterion.kernel_criterion_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

The finite sets A and B are disjoint; B has at most a times as many points as A. All displayed bounds use those same sets and parameters. The crossResidual is the sum of the short-distance residual w over A×B. KernelTest requires a strictly positive remaining gap R and the strict square comparison R²>4a(bA+1/L)(bB/p+1/L). The proof derives the required energy estimate from kernel positive semidefiniteness rather than assuming it. For a positive prime exponent a, A is D(m) and B is pD(n/p), with pᵃ∥n. At a=0 the prime-power criterion follows directly from the bound on Hhat(m) and nonnegativity of the residual.

## References

- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/KernelCriterion.kernel_criterion_blocks`
- Dependency: [D5/S3/Arith/Divisors/ErdosNicolas/Basic](Basic.md)
- Dependency: [D5/S3/Arith/Divisors/ErdosNicolas/DivisorBlocks](DivisorBlocks.md)
- Dependency: [D5/S3/Arith/Divisors/ErdosNicolas/TentKernel](TentKernel.md)
