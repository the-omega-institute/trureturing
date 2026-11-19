# Interior observations, a common core and phase recovery

## Abstract

An actual raw interior three-site observation gives conditional full-state phase recovery against every actual bond-two competitor, using target-only spanning, positive definite actual environments and injective transfer.

**Definition 1.1 (Both actual exterior words).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.interiorColumns`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.interiorColumns` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For a state of length (p+k)+q, row u and column (a,b) contain the actual amplitude at append(append(a,u),b). Neither exterior is shifted, identified or summed coherently.

**Definition 1.2 (Raw interior Hermitian density).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.rawInterior`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.rawInterior` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The observation is C C† for these interior amplitude columns. It is unnormalized, preserves the norm-squared scale, and differs from the raw prefix observation and the coherent improper marginal.

**Definition 1.3 (Transposed trace coordinates).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.feature`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.feature` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The feature entry F(u,(i,j)) is A_u(j,i). Therefore F times the coordinate vector X(i,j) is gamma A k X, where gamma is the original trace(X A_u). No conjugation is applied to X.

**Definition 1.4 (Actual left and right contexts).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.context`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.context` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

K((i,j),(a,b))=(A_b r)(i)(l A_a)(j), with bilinear row l. The corresponding virtual coefficient is A_b (r l) A_a. Matrix multiplication gives C=F K for every actual realization, including singular competitors.

**Definition 1.5 (The left environment transfer).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.dualTransfer`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.dualTransfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The map sends X to the sum of A_i† X A_i. Write P=(dualTransfer A)^p(l†l), H=(transfer A)^q(rr†). Snoc induction over original words gives prefixMap† prefixMap=P; the original right tail_gram supplies H. The finite context dictionary is K K†=H tensor P-transpose, and the exact observed density is F (H tensor P-transpose) F†. The transpose and the order of the two exterior words are essential.

**Theorem 1.6 (The actual left Gram dictionary).**

$$\forall (A: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (l: \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (p: \mathbb{N}), (\operatorname{Matrix.mul}\left(\operatorname{Matrix.conjTranspose}\left(\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery.prefixMap}\left(A, l, p\right)\right), \operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery.prefixMap}\left(A, l, p\right)\right) = \operatorname{Function.iterate}\left(\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.dualTransfer}\left(A\right), p, \operatorname{Matrix.vecMulVec}\left(\operatorname{star}\left(l\right), l\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.left_boundary_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every finite p, prefixMap dagger times prefixMap is the p-fold dual transfer of the actual bilinear boundary Gram. This is the original snoc-induction supplier, exposed with its proof unchanged for the root-realization consumer; it is not new mathematics in that consumer.

**Theorem 1.7 (The entire actual interior Gram dictionary).**

$$\forall (A: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (l: \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (r: \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (p: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (q: \mathbb{N}), (\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.rawInterior}\left(p, k, q, \operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.mpsState}\left(p + k + q, A\left(0\right), A\left(1\right), l, r\right)\right) = \operatorname{Matrix.mul}\left(\operatorname{Matrix.mul}\left(\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.feature}\left(A, k\right), \operatorname{Matrix.kronecker}\left(\operatorname{Function.iterate}\left(\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery.transfer}\left(A\right), q, \operatorname{Matrix.vecMulVec}\left(r, \operatorname{star}\left(r\right)\right)\right), \operatorname{Matrix.transpose}\left(\operatorname{Function.iterate}\left(\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.dualTransfer}\left(A\right), p, \operatorname{Matrix.vecMulVec}\left(\operatorname{star}\left(l\right), l\right)\right)\right)\right)\right), \operatorname{Matrix.conjTranspose}\left(\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.feature}\left(A, k\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.interior_density_dictionary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every finite p,k,q, rawInterior is feature times the Kronecker product of the right environment and transposed left environment times feature dagger. The original proof is unchanged. The root-realization consumer specializes k=2 while retaining all exterior words and all raw matrix entries.

**Theorem 1.8 (Every virtual coefficient propagates).**

$$\forall (A: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (B: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), ((\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.TwoSiteSpanning}\left(A\right)) \to ((\forall (X: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\exists (Y: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.gamma}\left(B, 3, X\right) = \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.gamma}\left(A, 3, Y\right)))) \to (\forall (m: \mathbb{N}), (\forall (X: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\exists (Y: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.gamma}\left(B, m + 3, X\right) = \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.gamma}\left(A, m + 3, Y\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.all_coefficient_parent_induction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For arbitrary A,B with TwoSiteSpanning A, assume every three-site gamma B 3 X belongs to the target gamma image. For every natural m and every complex two by two X, there is Y with gamma B (m+3) X=gamma A (m+3) Y. The induction generalizes X. Its snoc branch uses B_j X through trace cyclicity, its cons branch uses X B_i. Both slices belong to the same actual function gamma B (m+4) X, so the original unrestricted parent_intersection applies. The statement imposes no physical cyclicity, shifted marginal or competitor regularity.

**Theorem 1.9 (A common core for every actual competitor).**

$$\forall (A: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (B: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (l: \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (r: \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (lprime: \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (rprime: \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (p: \mathbb{N}), (\forall (q: \mathbb{N}), ((1 \le p) \to ((1 \le q) \to ((\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.TwoSiteSpanning}\left(A\right)) \to ((\operatorname{Matrix.PosDef}\left(\operatorname{Function.iterate}\left(\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.dualTransfer}\left(A\right), p, \operatorname{Matrix.vecMulVec}\left(\operatorname{star}\left(l\right), l\right)\right)\right)) \to ((\operatorname{Matrix.PosDef}\left(\operatorname{Function.iterate}\left(\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery.transfer}\left(A\right), q, \operatorname{Matrix.vecMulVec}\left(r, \operatorname{star}\left(r\right)\right)\right)\right)) \to ((\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.rawInterior}\left(p, 3, q, \operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.mpsState}\left(p + 3 + q, B\left(0\right), B\left(1\right), lprime, rprime\right)\right) = \operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.rawInterior}\left(p, 3, q, \operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.mpsState}\left(p + 3 + q, A\left(0\right), A\left(1\right), l, r\right)\right)) \to (\exists (X: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.mpsState}\left(p + 3 + q, B\left(0\right), B\left(1\right), lprime, rprime\right) = \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.gamma}\left(A, p + 3 + q, X\right))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.interior_common_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Let p,q be at least one and N=(p+3)+q. Only the target A satisfies TwoSiteSpanning and positive definiteness of P,H. The competitor B and its two free boundaries are entirely arbitrary. Equality of their raw interior observations implies that the entire actual competitor state is gamma A N X for one unrestricted complex two by two coefficient X. No transfer inverse, common-core premise, coefficient-image equality, rank-one premise or regularity of B is assumed.

**Theorem 1.10 (Rank-one obstruction for an actual common core).**

$$\forall (A: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (B: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (lprime: \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (rprime: \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (N: \mathbb{N}), (\forall (X: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), ((4 \le N) \to ((\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.TwoSiteSpanning}\left(A\right)) \to ((\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.mpsState}\left(N, B\left(0\right), B\left(1\right), lprime, rprime\right) = \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.gamma}\left(A, N, X\right)) \to ((\operatorname{Matrix.rank}\left(X\right) \le 1) \land (\exists (lA: \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\exists (rA: \operatorname{Fin}\left(2\right) \to \mathbb{C}), ((X = \operatorname{Matrix.vecMulVec}\left(rA, lA\right)) \land (\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.mpsState}\left(N, B\left(0\right), B\left(1\right), lprime, rprime\right) = \operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.mpsState}\left(N, A\left(0\right), A\left(1\right), lA, rA\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.common_core_rank_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Let N be at least four and suppose an actual free-boundary binary bond-two competitor equals gamma A N X for a TwoSiteSpanning target core A. The weighted two-site flattening of gamma A N X is a submatrix of the competitor's amplitude-column matrix, so its rank is at most two. If X were invertible, left multiplication by X would preserve the four-dimensional two-site span and give rank four, a contradiction. Hence rank X is at most one, including X=0; the existing rank-one factorization and the private state-gamma identity then refactor the same competitor through A with arbitrary new boundaries. This adds no transfer, positivity, phase, genericity, dynamical or thermodynamic premise.

**Theorem 1.11 (Conditional interior phase recovery for arbitrary competitors).**

$$\forall (A: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (B: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Bond}), (\forall (l: \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (r: \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (lprime: \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (rprime: \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (p: \mathbb{N}), (\forall (q: \mathbb{N}), ((1 \le p) \to ((1 \le q) \to ((\operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.TwoSiteSpanning}\left(A\right)) \to ((\operatorname{Function.Injective}\left(\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery.transfer}\left(A\right)\right)) \to ((\operatorname{Matrix.PosDef}\left(\operatorname{Function.iterate}\left(\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.dualTransfer}\left(A\right), p, \operatorname{Matrix.vecMulVec}\left(\operatorname{star}\left(l\right), l\right)\right)\right)) \to ((\operatorname{Matrix.PosDef}\left(\operatorname{Function.iterate}\left(\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery.transfer}\left(A\right), q, \operatorname{Matrix.vecMulVec}\left(r, \operatorname{star}\left(r\right)\right)\right)\right)) \to ((\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.rawInterior}\left(p, 3, q, \operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.mpsState}\left(p + 3 + q, B\left(0\right), B\left(1\right), lprime, rprime\right)\right) = \operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.rawInterior}\left(p, 3, q, \operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.mpsState}\left(p + 3 + q, A\left(0\right), A\left(1\right), l, r\right)\right)) \to (\exists (z: \mathbb{C}), ((\operatorname{norm}\left(z\right) = 1) \land (\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.mpsState}\left(p + 3 + q, B\left(0\right), B\left(1\right), lprime, rprime\right) = \operatorname{HSMul.hSMul}\left(z, \operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.mpsState}\left(p + 3 + q, A\left(0\right), A\left(1\right), l, r\right)\right))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.interior_phase_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Let p,q be at least one and N=(p+3)+q. Assume only the target core A has TwoSiteSpanning and injective complex-linear transfer, with its actual P,H positive definite. For arbitrary competitor core B and arbitrary free boundaries lprime,rprime, equality of the entire unnormalized rawInterior p 3 q matrices implies that the actual full competitor is z times the target for one complex z of norm one. The proof first uses interior_common_core and common_core_rank_one without altering their statements. No same-core, rank-one or competitor regularity premise is added to this endpoint.

After refactorization through A, cancel F W F† using a private sandwich lemma with four columns indexed by Fin 2 times Fin 2; the original two-column sandwich lemma cannot apply here. The dictionary gives W=H tensor P-transpose, with entry H(i,k) P(t,j). Scalar linearity and transfer injectivity cancel the q-fold right iterate. The bilinear trace identity trace(Y E(X))=trace(Edual(Y) X), finite-dimensional surjectivity of E, and trace extensionality give injectivity of Edual, so the p-fold left iterate cancels as well. No positivity, p≥1 or q≥1 is used within this same-core phase argument.

The resulting entries are precisely equality of the outer Grams of the flattened coefficients x(i,j)=r(i)l(j). A consumed private dimension-generic version of the original boundary_phase argument handles x=0 before selecting a nonzero coordinate, and gives xhat=z x with norm(z)=1. The unchanged state-gamma identity and trace linearity propagate z to the entire state. This preserves the bilinear left boundary and the P transpose; no reciprocal positive factors, square roots or positivity of competitor environments are required.

Positive definiteness makes det(H tensor P-transpose) nonzero by the existing Kronecker determinant theorem. The context has full row rank four. Original trace_separates makes the target three-site feature injective, hence the observed column range is precisely the four-dimensional target parent space. Original gram_range transfers this range to the competitor. Its observed dimension four saturates the entire competitor coefficient image, whose dimension is at most four; this establishes the all-coefficient induction hypothesis. Apply that induction at m=p+q and coefficient r′ l′ to obtain the actual full competitor.

The rank-one result is conditional on the already established common-core representation and N≥4. It is a coefficient-rank statement for actual free-boundary points; it does not by itself recover the boundary phase, prove transfer injectivity, extend to the closure of the MPS image, or settle Critch–Morton Conjecture 9.

The theorem interior_common_core alone supplies the common-core representation; common_core_rank_one now proves rank X≤1 and free-boundary refactorization under N≥4 and TwoSiteSpanning A. Conditional interior phase recovery is supplied by interior_phase_recovery; intrinsic interior genericity and Critch–Morton Conjecture 9 remain unproved, and this unit earns no solved-open-problem credit. The imported Conjecture 8 canonical reconstruction remains attributed to Haobo Ma and Wenlin Zhang, Proof of Critch–Morton Conjecture 8 (3 November 2026), CC BY 4.0; it is not new interior recovery mathematics. No normalization, physical recovery operation, dynamics, time group, energy, clock or thermodynamic cost is asserted.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.all_coefficient_parent_induction`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.common_core_rank_one`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.context`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.dualTransfer`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.feature`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.interiorColumns`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.interior_common_core`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.interior_density_dictionary`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.interior_phase_recovery`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.left_boundary_gram`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore.rawInterior`
- Dependency: [D5/S3/Quantum/Schatten/RankOneHadamard](../Schatten/RankOneHadamard.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery](OpenBoundaryMPSDensityRecovery.md)
