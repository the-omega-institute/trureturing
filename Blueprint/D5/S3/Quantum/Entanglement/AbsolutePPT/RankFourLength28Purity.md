# Length 28 with rank-four information

## Abstract

A length-28 arbitrary-spectrum purity estimate from two rank-three pencils and one rank-four mass inequality.

**Definition 1.1 (Uniform rank-four mass difference).**

$$\forall (lambda:Fin\left(28\right)\Rightarrow\mathbb{R}), L4\left(lambda\right)=sumLast\left(10, lambda\right)-sumFirst\left(6, lambda\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity.L4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinates are zero-based in Lean. L4 is the sum at indices 18 through 27 minus the sum at indices 0 through 5. The boundary vector is exactly lambda at 0,1,2,22,23,24,25,26,27, and K1 and K2 are the existing QutritSpectralReduction definitions applied to that vector.

**Theorem 1.2 (Arbitrary-spectrum purity estimate).**

$$\forall (lambda:Fin\left(28\right)\Rightarrow\mathbb{R}), ((Antitone\left(lambda\right))\land (\forall (i:Fin\left(28\right)), 0\leq lambda\left(i\right))\land (sum\left(lambda\right)=1)\land (PosSemidef\left(K1\left(boundary\left(lambda\right)\right)\right))\land (PosSemidef\left(K2\left(boundary\left(lambda\right)\right)\right))\land (0\leq L4\left(lambda\right)))\Rightarrow sumSquares\left(lambda\right)\leq \frac{1}{25}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity.purity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every antitone real vector lambda of length 28 with all entries nonnegative and total mass one, positivity of both boundary pencils and nonnegativity of L4 imply sumSquares(lambda) <= 1/25. Here sumSquares is the sum of all 28 squared entries. There is no restriction on the number of distinct entries. Let x_i=lambda_i-lambda_(i+1), with x_28=lambda_28 in one-based notation, and let y=(x_2,...,x_27,x_1-2*x_28). The exact rational identity is mass^2/25-purity = y^T P y + x^T H x + sum_(s,i) x_i Tr(B_(s,i) K_s) + L4 w^T x + sum_(a,s) q_a Tr(D_(a,s) K_s) + L4 sum_a gamma_a q_a + sum_s Tr(C_s S_s) + Tr(C_2 T). Both pencil indices are zero-based in this identity. All matrix products use full trace multiplicities, including both off-diagonal entries. P,B,D,C are positive semidefinite by rational LDL factors, while H,w,gamma and the endpoint rank-one weights are entrywise nonnegative. H is not assumed positive semidefinite. The Schur and mixed matrices are defined with v=(1,1,0) and columns of U equal to (1,-1,0),(0,0,1), with no normalization: q_s=v^T K_s v, d_s=U^T K_s U, b_s=U^T K_s v, S_s=q_s d_s-b_s b_s^T and T=q_0 d_1+q_1 d_0-b_0 b_1^T-b_1 b_0^T. DivisionFreeSchur supplies their positivity even for q_s=0. PSD trace pairing and x>=0 then make every summand nonnegative. The single data source is RankFourLength28Data.certificate. The equality spectrum (3,1^27)/30 has purity 1/25 and L4=1/15. This is a spectral relaxation theorem; it does not assert rank-three sufficiency, a literal APPT characterization, physical attainment, or the full APPT conjecture.

**Definition 1.3 (The implication with rank-four information omitted).**

$$\forall (lambda:Fin\left(28\right)\Rightarrow\mathbb{R}), ((Antitone\left(lambda\right))\land (\forall (i:Fin\left(28\right)), 0\leq lambda\left(i\right))\land (sum\left(lambda\right)=1)\land (PosSemidef\left(K1\left(boundary\left(lambda\right)\right)\right))\land (PosSemidef\left(K2\left(boundary\left(lambda\right)\right)\right)))\Rightarrow sumSquares\left(lambda\right)\leq \frac{1}{25}$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim retains arbitrary ordered nonnegative length-28 real spectra, mass one, and both original pencils. It omits only the L4 hypothesis. Its type is literally Prop.

**Theorem 1.4 (Both rank-three pencils alone are insufficient).**

$$Not\left(claim\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spectrum with nine entries 2/37 and nineteen entries 1/37 is ordered, nonnegative and has mass one. Both boundary pencils equal (3I-J)/37 and are positive semidefinite. Its purity is 55/1369 = 1/25 + 6/34225, whereas L4=-2/37. Thus the rank-four hypothesis supplies information needed by the stated spectral implication. The result has the literal type Not claim. It refutes neither APPT nor the APPT purity conjecture.

UniformRankFourNecessary proves a fixed rank-four test for arbitrary local dimensions m,n >= 4. Its product corner has six negative and ten positive partial-transpose eigenvectors, with the remaining vectors in the kernel. The actual diagonal APPT hypothesis implies sumFirst 6 <= sumLast 10 without ordering or mass assumptions. At m*n=28 this is exactly L4>=0. No arbitrary-r theorem is supplied. A physical 4 by 7 application requires one sorted diagonal APPT spectrum on which both pencil conditions and L4 are established, as well as an independent attainment construction. An existential spectrum providing only the pencils does not supply that common diagonal APPT hypothesis. Those physical implications are separate from the relaxation proved here.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity.L4`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity.purity_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Data](RankFourLength28Data.md)
- Dependency: [D5/S3/Quantum/Matrix/DivisionFreeSchur](../../Matrix/DivisionFreeSchur.md)
