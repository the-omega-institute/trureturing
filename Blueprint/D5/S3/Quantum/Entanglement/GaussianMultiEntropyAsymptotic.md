# Gaussian replica determinants

## Abstract

Twisting the replica coordinates of a real Gaussian state produces a positive-definite quadratic form. Its determinant evaluates the literal product integral.

**Definition 1.1 (The averaged precision).**

$$H_{\varepsilon}=1-(1-\varepsilon)\frac{P_0+P_1}{2}$$

*Formalization.* `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let N be the positive total number of modes and m the number of replicas. P is the matrix with all entries 1/N, the orthogonal projection onto constant mode coordinates. On replica coordinates, P_0 = I_m tensor P. If U maps x to its primed coordinates under the party permutations, P_1 = U^T P_0 U and T = (P_0 + P_1)/2. The matrix H_epsilon is I - (1-epsilon) T. The reindexing defining P_1 uses the inverse coordinate permutation on both matrix indices.

**Theorem 1.2 (The replica projection formula).**

$$Z(\alpha(1-(1-\varepsilon)P))=\sqrt{\frac{\varepsilon^{m}}{\operatorname{det}(H_{\varepsilon})}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.replica_integral_projection_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite replica type, every list of party sizes with positive total, and every permutation of the replicas for each party, assume alpha > 0 and 0 < epsilon <= 1. The replica contraction is the Lebesgue integral of the product of the Gaussian density kernels with precision alpha times (I - (1-epsilon) P). It equals sqrt(epsilon^m / det H_epsilon). Empty replica types and zero-sized individual parties are included. Uncurrying the replica variables preserves their product Lebesgue measure. The exponent becomes the quadratic form of alpha H_epsilon. The determinant of the single-copy precision is alpha^N epsilon, and the common alpha and pi factors cancel.

**Theorem 1.3 (The physical parameter range).**

$$\alpha=a-e^{-},\quad\varepsilon=\frac{a+(N-1)e^{-}}{\alpha},\quad0<\alpha,\quad0<\varepsilon\leq1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.symmetric_parameters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a >= 1 and N >= 3, the fully symmetric state's off-diagonal entry e^- is nonpositive and a + (N-1)e^- is positive. Thus alpha = a-e^- is positive, and epsilon = (a+(N-1)e^-)/alpha lies in (0,1]. The two square-root comparisons follow from the differences of their squares; the upper comparison is strict even at a = 1.

**Theorem 1.4 (The fully symmetric precision).**

$$W=\alpha(1-(1-\varepsilon)P)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.W_projection_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive mode count N and every a with a-e^- nonzero, the matrix W with diagonal a and off-diagonal e^- equals alpha times (I-(1-epsilon)P), with alpha and epsilon as above. Transporting this identity to the tagged party coordinates gives the same precision for the replica integral.

**Theorem 1.5 (One replica is normalized).**

$$Z_1=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.replica_integral_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any positive-definite real matrix on the party coordinates, a finite singleton replica type has contraction equal to one. Every party twist fixes its single replica. The averaged precision is the original block precision, so the determinant ratio equals one.

**Theorem 1.6 (Reduction to replica coordinates).**

$$\forall R \in \operatorname{FiniteTypes}\left(\right), \forall p \in \operatorname{List}\left(\mathbb{N}\right), \forall g \in \operatorname{Perm}\left(R\right)^{\operatorname{length}\left(p\right)}, \forall \varepsilon \in \mathbb{R}, 0<\operatorname{sum}\left(p\right),\quad0<\varepsilon\implies \operatorname{det}(\operatorname{H}\left(p, g, \varepsilon\right))=\operatorname{det}(\frac{(1+\varepsilon)^2}{4}I_R-\frac{(1-\varepsilon)^2}{4}\operatorname{Q}\left(p, g\right)^T\operatorname{Q}\left(p, g\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.replica_determinant_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite replica type R, any party list p with positive total N, any family g of replica permutations, and epsilon > 0, define Q(r,s) as the sum of 1/N over the modes whose party twist sends s to r. Then det H_epsilon equals the displayed determinant on R. The untwisted normalized indicator columns have entries [i=r]/sqrt(N), and their permuted columns have entries [i=g_k(r)]/sqrt(N). Both column families are orthonormal, their overlap is Q, and their outer products are the two constant-mode projections. The paired-column determinant identity gives the reduction.

**Theorem 1.7 (The entropy determinant expression).**

$$GM_n^{(3)}=\frac{1}{1-n}(\frac{1}{n}\log\phi_3-\frac{1}{2}(\log\phi_{AB:C}+\log\phi_{BC:A}+\log\phi_{CA:B}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.multi_entropy_determinant_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural replica order n, every positive tripartition, and a >= 1, put N = N_A + N_B + N_C and epsilon = (a+(N-1)e^-)/(a-e^-). Let Phi_3 be sqrt(epsilon^(n^2)/det H_epsilon) for the tripartite torus twists. Each Phi_R is sqrt(epsilon^n/det H_epsilon) for the corresponding bipartition and cyclic twist. Substituting the replica integrals and their one-replica normalizations into the entropy definitions gives the displayed identity. The replica-coordinate reduction applies to each of these four determinants.

**Theorem 1.8 (Binary replicas and bipartitions).**

$$\forall A \in \mathbb{N}, \forall B \in \mathbb{N}, \forall C \in \mathbb{N}, \forall \varepsilon \in \mathbb{R}, 0<A+B+C,\quad0<\varepsilon\implies \operatorname{det}(\operatorname{HAB}\left(A, B, C, \varepsilon\right))\operatorname{det}(\operatorname{HBC}\left(A, B, C, \varepsilon\right))\operatorname{det}(\operatorname{HCA}\left(A, B, C, \varepsilon\right))=\varepsilon^2\operatorname{det}(\operatorname{Hthree}\left(A, B, C, \varepsilon\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.replica_two_determinant_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural tripartition A, B, C with positive total and every epsilon > 0, the product of the three bipartite H determinants equals epsilon^2 times the tripartite H determinant at replica order two. Put x=A/N, y=B/N, z=C/N. The binary cyclic twist is a swap. Reindexing the tripartite torus by its four coordinates gives the real matrix with rows (z,y,x,0), (y,z,0,x), (x,0,z,y), and (0,x,y,z). The reduced bipartite matrices and this tripartite matrix satisfy the binary determinant identity with a=((1+epsilon)/2)^2 and b=((1-epsilon)/2)^2. Here a-b=epsilon.

**Theorem 1.9 (Vanishing binary multi-entropy).**

$$\forall A \in \mathbb{N}, \forall B \in \mathbb{N}, \forall C \in \mathbb{N}, \forall a \in \mathbb{R}, 0<A,\quad0<B,\quad0<C,\quad1\leq a\implies \operatorname{determinantGM}\left(2, A, B, C, a\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.determinantGM3_two_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all positive integer party sizes A, B, C and all a >= 1, determinantGM3(2,A,B,C,a) is exactly zero. The physical epsilon lies in (0,1], so each H is positive definite and its determinant is positive. Taking the logarithm of the binary determinant identity gives log det H_AB:C + log det H_BC:A + log det H_CA:B = 2 log epsilon + log det H_3. This relation cancels all four terms of the binary entropy expression.

**Definition 1.10 (The large-squeezing conjecture).**

$$\forall n \in \mathbb{N}, \forall A \in \mathbb{N}, \forall B \in \mathbb{N}, \forall C \in \mathbb{N}, 2\leq n,\quad0<A,\quad0<B,\quad0<C\implies \operatorname{IsEquivalent}\left(\operatorname{atTop}\left(\right), \operatorname{GM}\left(n, A, B, C\right), \operatorname{mul}\left(\frac{2-n}{2n}, \operatorname{log}\left(\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every integer replica order n >= 2 and every positive integer tripartition A, B, C, the genuine tripartite multi-entropy is asymptotically equivalent to ((2-n)/(2n)) log(a) as the real squeezing parameter a tends to positive infinity. At n = 2 the comparison function is identically zero, so equivalence means eventual exact vanishing.

**Theorem 1.11 (The large-squeezing asymptotic).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.result` (`✓ std3`). ∎

*Resolves.* `Problems/camargo-nishida-2026-gaussian-multientropy` (proved) by `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"camargo-nishida-2026-gaussian-multientropy","declaration_gid":"D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The conjecture holds for every replica order n >= 2 and every positive tripartition. At n = 2 the exact binary determinant identity gives zero multi-entropy for all a >= 1. For n > 2 the torus and cyclic twists connect their replicas and contain an identity twist. Their permutation averages have Gram matrices with constant fixed space, so each H determinant is epsilon times a continuous function positive at zero. Since a^2 epsilon(a) tends to (N-1)/N^2, log(epsilon(a)) is asymptotically equivalent to -2log(a). Substitution into the four determinant entropies gives the coefficient (2-n)/(2n); the remaining terms have finite limits.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.H`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.W_projection_formula`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.determinantGM3_two_eq_zero`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.multi_entropy_determinant_formula`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.replica_determinant_reduction`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.replica_integral_projection_formula`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.replica_integral_singleton`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.replica_two_determinant_identity`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.symmetric_parameters`
- Dependency: [D5/S3/Quantum/Entanglement/GaussianReplicaReduction](GaussianReplicaReduction.md)
