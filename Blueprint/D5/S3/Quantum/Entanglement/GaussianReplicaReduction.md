# Replica determinant reduction

## Abstract

The determinant of a mean of two finite-rank orthogonal projections depends on the overlap of their orthonormal column families.

**Theorem 1.1 (Determinant normalization).**

$$\int_{\mathbb{R}^n} \operatorname{exp}(-x^TMx) dx=\frac{\pi^{\frac{n}{2}}}{\sqrt{\operatorname{det}(M)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.integral_exp_neg_quadraticForm_pi` (`✓ std3`). ∎

*Citation.* Mario Brcic (2026). *AI Safety Formalization Atlas: multivariate Gaussian integrals and finite-product coordinates*. URL: <https://github.com/mbrcic/ai-safety-formalization-atlas/tree/254b6275b753efb609cd38ef4c85eef29b4a13b4>.

*Commentary.*

For every natural dimension n and positive-definite real n by n matrix M, the Lebesgue integral of exp(-x^T M x) over the plain coordinate space is pi^(n/2) divided by the square root of det M. Factor M as B^T B using its positive matrix square root. The linear substitution y = B x has Jacobian det B = sqrt(det M) and reduces the integral to the isotropic Euclidean Gaussian. The coordinate and Euclidean measures agree under the measure-preserving equivalence between their carriers.

**Theorem 1.2 (A scalar Schur complement).**

$$\forall R \in \operatorname{FiniteTypes}, \forall Q \in \mathbb{R}^{R\times R}, \forall a \in \mathbb{R}, \forall b \in \mathbb{R}, a\neq 0\implies \operatorname{det}(\operatorname{fromBlocks}\left(aI_R, -bQ, -bQ^{T}, aI_R\right))=\operatorname{det}(a^2I_R-b^2Q^{T}Q)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.scalar_block_determinant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type R, every real matrix Q on R, and real a and b with a nonzero, the displayed block determinant equals det(a^2 I_R - b^2 Q^T Q). Factor a from the first block row, then apply the Schur complement with identity in the upper left block. Absorbing a into the remaining determinant cancels the denominator.

**Theorem 1.3 (Two orthonormal column families).**

$$\forall J \in \operatorname{FiniteTypes}, \forall R \in \operatorname{FiniteTypes}, \forall U \in \mathbb{R}^{J\times R}, \forall V \in \mathbb{R}^{J\times R}, \forall b \in \mathbb{R}, U^{T}U=I_R,\quad V^{T}V=I_R,\quad1-b\neq 0\implies \operatorname{det}(I_J-b(UU^{T}+VV^{T}))=\operatorname{det}((1-b)^2I_R-b^2(U^{T}V)^{T}(U^{T}V))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.paired_projection_determinant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J and R be finite index types, and let U and V be real J by R matrices satisfying U^T U = V^T V = I_R. For any real b with 1-b nonzero, Sylvester's identity changes the determinant on J into the determinant of the Gram matrix of the concatenated columns. Its diagonal blocks are I_R and its off-diagonal blocks are U^T V and V^T U. The scalar Schur complement yields the displayed determinant on R.

**Theorem 1.4 (The binary determinant identity).**

$$\forall x \in \mathbb{R}, \forall y \in \mathbb{R}, \forall z \in \mathbb{R}, \forall a \in \mathbb{R}, \forall b \in \mathbb{R}, x+y+z=1\implies \operatorname{D}\left(a, b, \operatorname{A}\left(x, y, z\right)\right)\operatorname{D}\left(a, b, \operatorname{B}\left(x, y, z\right)\right)\operatorname{D}\left(a, b, \operatorname{C}\left(x, y, z\right)\right)=(a-b)^2\operatorname{D}\left(a, b, \operatorname{Q}\left(x, y, z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.binary_replica_determinant_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real x, y, z, a, b with x+y+z=1, let A have rows (z,x+y) and (x+y,z), B have rows (x,y+z) and (y+z,x), and C have rows (y,z+x) and (z+x,y). Let Q have rows (z,y,x,0), (y,z,0,x), (x,0,z,y), and (0,x,y,z). Define D(a,b,M) = det(a I - b M^T M). Then D(a,b,A) D(a,b,B) D(a,b,C) = (a-b)^2 D(a,b,Q). Expanding the determinants verifies this polynomial identity without any positivity assumption.

**Theorem 1.5 (Square roots at large arguments).**

$$\forall b \in \mathbb{R}, \forall c \in \mathbb{R}, 0\leq b,\quad0\leq b+c\implies \operatorname{lim}\left(\operatorname{div}\left(\operatorname{sqrt}\left(ba^2+c\right), a\right)\right)=\operatorname{sqrt}\left(b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.sqrt_quadratic_ratio_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real b and c with b nonnegative and b+c nonnegative, sqrt(b a^2+c)/a tends to sqrt(b) as a tends to positive infinity. For a at least one the radicand is nonnegative. Dividing inside the square root gives sqrt(b+c/a^2), and continuity gives the limit.

**Theorem 1.6 (The small symmetric parameter).**

$$\forall N \in \mathbb{R}, 2<N\implies \operatorname{lim}\left(a^2\varepsilon(a)\right)=\frac{N-1}{N^2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.symmetric_parameter_scaled_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real N greater than two, let e(a) = ((a^2-1)(N-2)-sqrt(a^2-1) sqrt((a^2-1)N^2+4(N-1)))/(2a(N-1)) and epsilon(a) = (a+(N-1)e(a))/(a-e(a)). Then a^2 epsilon(a) tends to (N-1)/N^2 as a tends to positive infinity. Set s=sqrt(a^2-1) and t=sqrt((a^2-1)N^2+4(N-1)). The identity (a+(N-1)e(a))a(sN+t)=t-(N-2)s removes cancellation in the numerator. The limits s/a=1, t/a=N and (a-e(a))/a=N/(N-1) give the result.

**Theorem 1.7 (The logarithm of a quadratically small parameter).**

$$\forall \varepsilon \in \mathbb{R}\to\mathbb{R}, \forall C \in \mathbb{R}, 0<C,\quad\operatorname{lim}\left(a^2\varepsilon(a)\right)=C\implies \operatorname{IsEquivalent}\left(\operatorname{atTop}\left(\right), \operatorname{log}\left(\varepsilon\right), -2\operatorname{log}\left(\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.log_equivalent_of_scaled_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real-valued function epsilon and any positive real C, if a^2 epsilon(a) tends to C at positive infinity, then log(epsilon(a)) is asymptotically equivalent to -2 log(a). The difference is eventually log(a^2 epsilon(a)), which tends to log(C). Every function with a finite limit is negligible compared with log(a).

**Theorem 1.8 (The maximum principle for replica twists).**

$$\forall R \in \operatorname{NonemptyFiniteTypes}\left(\right), \forall K \in \operatorname{Types}\left(\right), \forall M \in \mathbb{R}^{R\times R}, \forall g \in \operatorname{Perm}\left(R\right)^{K}, \operatorname{RowStochastic}\left(M\right),\quad\operatorname{PositiveTwistEntries}\left(M, g\right),\quad\operatorname{TransitiveTwistPaths}\left(g\right)\implies \operatorname{Fix}\left(M\right)=\operatorname{Constants}\left(R\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.stochastic_twist_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be a nonempty finite type, K any type, g a family of permutations of R, and M a real row-stochastic matrix on R. Assume M(r,g_k(r)) is positive for every k and r, and that every ordered pair of replicas is connected by a finite sequence of twists. Then Mx=x if and only if x is constant. Choose a coordinate where x attains its maximum. The weighted sum of the nonnegative differences from this maximum vanishes, so each positive transition also attains the maximum. Propagation along the twist paths makes every coordinate equal.

**Theorem 1.9 (The kernel of a permutation average).**

$$\forall R \in \operatorname{NonemptyFiniteTypes}\left(\right), \forall K \in \operatorname{FiniteTypes}\left(\right), \forall g \in \operatorname{Perm}\left(R\right)^{K}, \forall k_0 \in K, \operatorname{g}\left(k_0\right)=id,\quad\operatorname{TransitiveTwistPaths}\left(g\right)\implies \operatorname{RowStochastic}\left(Q^{T}Q\right),\quad\operatorname{Fix}\left(Q^{T}Q\right)=\operatorname{Constants}\left(R\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.permutation_average_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be a nonempty finite replica type and K a finite type indexing permutations g_k, with an index k_0 for the identity permutation. Assume their directed paths connect every ordered pair in R. Define Q(r,s) as the number of indices k with r=g_k(s), divided by the cardinality of K. Its row and column sums equal one. Thus Q^T Q is row-stochastic. Its entry at (r,g_k(r)) is positive: the summand at g_k(r) contains the k transition and the identity transition. The maximum principle shows that Q^T Q fixes exactly the constant real vectors.

**Theorem 1.10 (A simple determinant factor).**

$$\forall R \in \operatorname{NonemptyFiniteTypes}\left(\right), \forall G \in \mathbb{R}^{R\times R}, \operatorname{Hermitian}\left(G\right),\quad\operatorname{RowStochastic}\left(G\right),\quad\operatorname{Fix}\left(G\right)=\operatorname{Constants}\left(R\right)\implies \exists D \in \mathbb{R}\to\mathbb{R}, \operatorname{Continuous}\left(D\right),\quad0<\operatorname{D}\left(0\right),\quad\forall \varepsilon \in \mathbb{R}, \operatorname{det}(\frac{1+\varepsilon}{2}^2I_R-\frac{1-\varepsilon}{2}^2G)=\varepsilon\operatorname{D}\left(\varepsilon\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.stochastic_determinant_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real Hermitian row-stochastic matrix G on a nonempty finite type, assume its fixed vectors are exactly the constants. Then there is a continuous real function D with D(0)>0 such that det(((1+e)/2)^2 I-((1-e)/2)^2 G)=e D(e) for every real e. Gershgorin's theorem bounds every eigenvalue by one. The constant vector gives an eigenvalue one, and linear independence of the eigenbasis makes this eigenvalue simple. The remaining eigenvalues are strictly below one. The spectral theorem gives D as the product of the remaining factors, each positive at zero.

**Theorem 1.11 (The residual replica determinant).**

$$\forall R \in \operatorname{NonemptyFiniteTypes}\left(\right), \forall g \in \operatorname{FinitePermutationFamilies}\left(R\right), \operatorname{IdentityMember}\left(g\right),\quad\operatorname{TransitiveTwistPaths}\left(g\right)\implies \exists D \in \mathbb{R}\to\mathbb{R}, \operatorname{Continuous}\left(D\right),\quad0<\operatorname{D}\left(0\right),\quad\forall \varepsilon \in \mathbb{R}, \operatorname{det}(\frac{1+\varepsilon}{2}^2I_R-\frac{1-\varepsilon}{2}^2Q^{T}Q)=\varepsilon\operatorname{D}\left(\varepsilon\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.permutation_average_determinant_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite nonempty replica type and every finite family of permutations containing the identity and connecting every ordered pair by twist paths, let Q be their uniform permutation average. There exists a continuous D with D(0)>0 such that det(((1+e)/2)^2 I-((1-e)/2)^2 Q^T Q)=e D(e) for every real e. The Gram matrix is Hermitian and its fixed vectors are the constants, so its determinant has the simple factor just established.

**Theorem 1.12 (Paths on a replica cycle).**

$$\forall n \in \mathbb{N}, \forall K \in \operatorname{Types}\left(\right), \forall g \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right)^{K}, \operatorname{ContainsCyclicShift}\left(g\right)\implies \operatorname{TransitiveTwistPaths}\left(g\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.cyclic_twists_transitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and every family of permutations of Fin n containing the cyclic shift finRotate(n), the relation generated by the family connects every ordered pair. Iterating the cyclic shift by the residue s-r sends r to s. The empty cycle is included.

**Theorem 1.13 (Paths on a rectangular replica torus).**

$$\forall n \in \mathbb{N}, \forall m \in \mathbb{N}, \forall K \in \operatorname{Types}\left(\right), \forall g \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(m\right)\right)^{K}, \operatorname{ContainsBothCoordinateShifts}\left(g\right)\implies \operatorname{TransitiveTwistPaths}\left(g\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.torus_twists_transitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of natural dimensions n and m, a family of permutations of Fin n times Fin m that contains the cyclic shift in each coordinate connects every ordered pair. First move the first coordinate to its target, then move the second coordinate. Empty dimensions are included.

**Theorem 1.14 (The replica entropy asymptotic).**

$$\forall n \in \mathbb{N}, \forall \varepsilon \in \mathbb{R}\to\mathbb{R}, \forall C \in \mathbb{R}, \forall D \in \operatorname{FourContinuousRealFunctions}\left(\right), 2<n,\quad0<C,\quad\operatorname{lim}\left(a^2\varepsilon(a)\right)=C,\quad\operatorname{PositiveAtZero}\left(D\right)\implies \operatorname{IsEquivalent}\left(\operatorname{atTop}\left(\right), \operatorname{ReplicaEntropy}\left(n, \varepsilon, D\right), \frac{2-n}{2n}\operatorname{log}\left(\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.replica_entropy_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer n>2, suppose epsilon is a real-valued function with a^2 epsilon(a) tending to a positive C as a tends to positive infinity. Let D_0,D_1,D_2,D_3 be continuous real functions positive at zero. Define Phi_0(a)=sqrt(epsilon(a)^(n^2)/(epsilon(a)D_0(epsilon(a)))) and Phi_i(a)=sqrt(epsilon(a)^n/(epsilon(a)D_i(epsilon(a)))) for i=1,2,3. Then (log(Phi_0)/n-(log(Phi_1)+log(Phi_2)+log(Phi_3))/2)/(1-n) is asymptotically equivalent to ((2-n)/(2n))log(a). The exact logarithmic expression is ((n-2)/(4n))log(epsilon(a)) plus log(D_0(epsilon(a)))/(2n(n-1)) minus the sum of the other three logarithms divided by 4(n-1). The latter terms have finite limits, and log(epsilon(a)) is equivalent to -2log(a).

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.binary_replica_determinant_identity`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.cyclic_twists_transitive`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.integral_exp_neg_quadraticForm_pi`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.log_equivalent_of_scaled_limit`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.paired_projection_determinant`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.permutation_average_determinant_factor`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.permutation_average_kernel`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.replica_entropy_asymptotic`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.scalar_block_determinant`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.sqrt_quadratic_ratio_limit`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.stochastic_determinant_factor`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.stochastic_twist_kernel`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.symmetric_parameter_scaled_limit`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianReplicaReduction.torus_twists_transitive`
