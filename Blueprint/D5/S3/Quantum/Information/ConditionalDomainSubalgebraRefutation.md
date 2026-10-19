# Two-qubit conditional domains need not be subalgebras

## Abstract

A two-qubit density matrix with invertible marginals has a conditional domain that is not closed under multiplication.

The first tensor factor is A and the second is B, both equal to the complex two-by-two matrix algebra. Fin(2) consists of 0 and 1; pairs index the computational basis (00, 01, 10, 11). Matrix multiplication and the Kronecker product act in this order of factors, and 1 is the identity matrix. Every sum below ranges over Fin(2). The partial trace over B has (a,c)-entry the sum of X((a,b),(c,b)) over b; the partial trace over A has (b,d)-entry the sum of X((a,b),(a,d)) over a. The displayed lambda expressions give these matrices explicitly. Commute(X,Y) means XY = YX. DensityState consists of positive semidefinite complex matrices of trace one, and nu.1 is the underlying matrix. IsUnit means invertible. StarSubalgebra denotes a complex unital subalgebra closed under conjugate transpose; its cast to Set is its carrier.

**Definition 1.1 (The conditional domain in B).**

$$\forall (\nu: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\operatorname{conditionalDomainB}\left(\nu\right) = \{B: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right) \mid \operatorname{Commute}\left(\lambda (a: \operatorname{Fin}\left(2\right)) \mapsto (\lambda (c: \operatorname{Fin}\left(2\right)) \mapsto (\sum_{(b: \operatorname{Fin}\left(2\right))} (\nu\left((a, b), (c, b)\right)))), \lambda (a: \operatorname{Fin}\left(2\right)) \mapsto (\lambda (c: \operatorname{Fin}\left(2\right)) \mapsto (\sum_{(b: \operatorname{Fin}\left(2\right))} (\left((\nu) \cdot (\operatorname{Matrix.kronecker}\left((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), B\right))\right)\left((a, b), (c, b)\right))))\right)\})$$

*Formalization.* `D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.conditionalDomainB` (`✓ std3`).

*Citation.* Arthur J. Parzygnat (2021). *Conditional Distributions for Quantum Systems*. DOI: [10.4204/EPTCS.343.1](https://doi.org/10.4204/EPTCS.343.1). URL: <https://arxiv.org/abs/2102.01529v3>.

*Commentary.*

Definition 5.5 defines B_nu as the set of B for which tr_B(nu(1 tensor B)) commutes with the marginal rho = tr_B(nu). The first lambda expression is rho, and the second is tr_B(nu(1 tensor B)). This definition applies to any joint matrix nu, without positivity or invertibility assumptions.

**Definition 1.2 (The conditional domain in A).**

$$\forall (\nu: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\operatorname{conditionalDomainA}\left(\nu\right) = \{A: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right) \mid \operatorname{Commute}\left(\lambda (b: \operatorname{Fin}\left(2\right)) \mapsto (\lambda (d: \operatorname{Fin}\left(2\right)) \mapsto (\sum_{(a: \operatorname{Fin}\left(2\right))} (\nu\left((a, b), (a, d)\right)))), \lambda (b: \operatorname{Fin}\left(2\right)) \mapsto (\lambda (d: \operatorname{Fin}\left(2\right)) \mapsto (\sum_{(a: \operatorname{Fin}\left(2\right))} (\left((\operatorname{Matrix.kronecker}\left(A, (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))\right)) \cdot (\nu)\right)\left((a, b), (a, d)\right))))\right)\})$$

*Formalization.* `D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.conditionalDomainA` (`✓ std3`).

*Citation.* Arthur J. Parzygnat (2021). *Conditional Distributions for Quantum Systems*. DOI: [10.4204/EPTCS.343.1](https://doi.org/10.4204/EPTCS.343.1). URL: <https://arxiv.org/abs/2102.01529v3>.

*Commentary.*

Definition 5.5 defines A_nu as the set of A for which tr_A((A tensor 1)nu) commutes with the marginal sigma = tr_A(nu). The first lambda expression is sigma, and the second is tr_A((A tensor 1)nu). The multiplication order agrees with Definition 5.5, and the definition applies to every joint matrix nu.

**Definition 1.3 (The two-qubit subalgebra suspicion).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (\nu: \operatorname{DensityState}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))\right)), ((\operatorname{IsUnit}\left(\lambda (a: \operatorname{Fin}\left(2\right)) \mapsto (\lambda (c: \operatorname{Fin}\left(2\right)) \mapsto (\sum_{(b: \operatorname{Fin}\left(2\right))} (\nu.1\left((a, b), (c, b)\right))))\right)) \Rightarrow ((\operatorname{IsUnit}\left(\lambda (b: \operatorname{Fin}\left(2\right)) \mapsto (\lambda (d: \operatorname{Fin}\left(2\right)) \mapsto (\sum_{(a: \operatorname{Fin}\left(2\right))} (\nu.1\left((a, b), (a, d)\right))))\right)) \Rightarrow (\exists (S: \operatorname{StarSubalgebra}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)), (\exists (T: \operatorname{StarSubalgebra}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)), (((S: \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)) = \operatorname{conditionalDomainB}\left(\nu.1\right)) \land ((T: \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)) = \operatorname{conditionalDomainA}\left(\nu.1\right))))))))$$

*Formalization.* `D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.claim` (`✓ std3`).

*Citation.* Arthur J. Parzygnat (2021). *Conditional Distributions for Quantum Systems*. DOI: [10.4204/EPTCS.343.1](https://doi.org/10.4204/EPTCS.343.1). URL: <https://arxiv.org/abs/2102.01529v3>.

*Commentary.*

Footnote 13, following Example 5.10, suspects that both conditional domains of a four-by-four density matrix are C*-subalgebras. With two nontrivial factors, both factors are two-by-two matrix algebras. The setting of Corollary 4.5 requires both marginals to be invertible. Thus the statement quantifies over every two-qubit density state with both marginal invertibility conditions and asks for a unital star subalgebra with carrier B_nu and another with carrier A_nu. In finite dimension every linear subspace is norm closed, so these unital star subalgebras are C*-subalgebras. Lemma 5.8 already gives the operator-system properties of the domains.

**Theorem 1.4 (Failure of multiplication closure with invertible marginals).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/parzygnat-2021-two-qubit-conditional-domain-refutation` (refuted) by `D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"parzygnat-2021-two-qubit-conditional-domain-refutation","declaration_gid":"D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Arthur J. Parzygnat (2021). *Conditional Distributions for Quantum Systems*. DOI: [10.4204/EPTCS.343.1](https://doi.org/10.4204/EPTCS.343.1). URL: <https://arxiv.org/abs/2102.01529v3>.

*Commentary.*

In the basis (00, 01, 10, 11), take nu = (1/32) [[11,1,1,0], [1,7,0,-1], [1,0,9,-1], [0,-1,-1,5]]. Let v_0 = (1,1,0,0)^T, v_1 = (1,0,1,0)^T, v_2 = (0,1,0,-1)^T and v_3 = (0,0,1,-1)^T. Then nu equals (diag(9,5,7,3) + v_0 v_0^dagger + v_1 v_1^dagger + v_2 v_2^dagger + v_3 v_3^dagger)/32. Each of the four outer products is positive semidefinite and has rank one. The diagonal term is positive semidefinite as well. Consequently nu is positive semidefinite, and its trace is (11+7+9+5)/32 = 1.

The marginal rho = tr_B(nu) is diag(9/16,7/16), and sigma = tr_A(nu) is diag(5/8,3/8). Their diagonal entries are nonzero, so both marginals are invertible.

For B = [[a,b],[c,d]], the matrix tr_B(nu(1 tensor B)) equals (1/32) [[11a+b+c+7d,a-d], [a-d,9a-b-c+5d]]. The matrix units E_01 = [[0,1],[0,0]] and E_10 = [[0,0],[1,0]] both give diag(1/32,-1/32), which commutes with rho. Thus both belong to B_nu. Their product is E_00 = [[1,0],[0,0]]. For E_00 the transformed matrix has off-diagonal entries 1/32, so it does not commute with rho, whose diagonal entries are distinct. Hence E_00 does not belong to B_nu.

A subalgebra containing E_01 and E_10 must contain their product E_00. Therefore no unital star subalgebra has carrier B_nu for this density state. This contradicts the first of the two carrier equalities in claim, while both marginal invertibility hypotheses hold.

## References

- Truth anchor: `D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.conditionalDomainA`
- Truth anchor: `D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.conditionalDomainB`
- Truth anchor: `D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
