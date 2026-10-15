# Finite-entropy relative entropy and a fixed reference

## Abstract

Bounded trace logarithms define relative entropy on normalized states with finite self entropy.

**Theorem 1.1 (Actual bounded logarithms and literal trace).**

$$\forall H \in CompleteComplexHilbertSpace, rho \in \operatorname{Reference}\left(H\right), sigma \in \operatorname{Reference}\left(H\right),\; \operatorname{AllGridShiftsStrictlyPositiveBoundedTraceClassCyclicAndEnergyCancellation}\left(rho, sigma\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/FiniteEntropyRelativeEntropy.traceLogGrid_operators` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. E. Shirokov (2012). *On a conjectured property of the von Neumann entropy valid in the commutative case*. URL: <https://arxiv.org/abs/1201.1093v1>.

*Commentary.*

Let H be any complete complex Hilbert space. References are actual positive trace-class contractions. For epsilon=1/(n+1), the shifts rho+epsilon I and sigma+epsilon I are strictly positive. Their CFC logarithms are bounded operators, with the usual operator-norm bounds. Both products of their difference with rho are trace class. The pairing equals the real trace with rho on the left by bounded-factor cyclicity.

The scalar log(1+epsilon) I cancels additively between the two regularizations. Thus the actual trace-log grid is cross regularized energy minus self regularized energy. No logarithm product law or commutation is used.

**Theorem 1.2 (A trace-log liminf with an extended energy characterization).**

$$\forall H \in CompleteComplexHilbertSpace, rho \in \operatorname{Reference}\left(H\right), sigma \in \operatorname{Reference}\left(H\right),\; \left(\operatorname{PositiveTraceOne}\left(rho\right) \land \left(\operatorname{PositiveTraceOne}\left(sigma\right) \land \operatorname{Finite}\left(\operatorname{spectralEntropy}\left(rho\right)\right)\right)\right) \Rightarrow \operatorname{finiteEntropyRelativeEntropy}\left(rho, sigma\right) = \operatorname{tsub}\left(\operatorname{spectralEnergy}\left(sigma, rho\right), \operatorname{spectralEntropy}\left(rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/FiniteEntropyRelativeEntropy.finiteEntropyRelativeEntropy_eq_energy_tsub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. E. Shirokov (2012). *On a conjectured property of the von Neumann entropy valid in the commutative case*. URL: <https://arxiv.org/abs/1201.1093v1>.

*Commentary.*

finiteEntropyRelativeEntropy is defined only with proofs that both actual real traces are one and that the spectral entropy of rho is finite. Its defining value is the ENNReal liminf of ofReal of the actual bounded trace-log grid. The definition contains no spectral-energy subtraction or energy-finiteness branch.

Each of the two ofReal regularized-energy sequences increases to its actual spectral energy. The same monotone convergence proof is used twice. Nonnegativity of self regularized energy gives ofReal(a-b)=ofReal(a)-ofReal(b). ENNReal subtraction is continuous at a finite second limit, even when the first limit is infinity. The resulting limit proves that the liminf equals E_sigma(rho)-S(rho). Infinite-entropy states are outside this definition's domain.

**Theorem 1.3 (Finite value, support obstruction and trace-norm separation).**

$$\forall H \in CompleteComplexHilbertSpace, rho \in \operatorname{Reference}\left(H\right), sigma \in \operatorname{Reference}\left(H\right),\; \left(\operatorname{PositiveTraceOne}\left(rho\right) \land \left(\operatorname{PositiveTraceOne}\left(sigma\right) \land \operatorname{Finite}\left(\operatorname{spectralEntropy}\left(rho\right)\right)\right)\right) \Rightarrow \operatorname{FiniteUnclampedValueNormSquareLowerBoundAndInfiniteEnergyOrKernelFailureTop}\left(rho, sigma\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/FiniteEntropyRelativeEntropy.finiteEntropyRelativeEntropy_branches` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. E. Shirokov (2012). *On a conjectured property of the von Neumann entropy valid in the commutative case*. URL: <https://arxiv.org/abs/1201.1093v1>.

*Commentary.*

At finite cross energy the divergence equals ofReal(E.toReal-S.toReal). The Hellinger energy theorem for actual trace-one states proves norm(rho-sigma) squared divided by four <= E.toReal-S.toReal. Consequently this is an unclamped nonnegative real value and is the actual real value of the divergence.

Infinite cross energy gives infinity because self entropy is finite. If ker(sigma) is not contained in ker(rho), the existing finite-energy kernel theorem excludes finite cross energy, so divergence is infinity. Kernel inclusion alone is not asserted sufficient for finite energy. No use of the totalized real value of infinity represents an infinite relative entropy.

**Theorem 1.4 (An absolutely summable signed full spectral formula).**

$$\forall H \in CompleteComplexHilbertSpace, rho \in \operatorname{Reference}\left(H\right), sigma \in \operatorname{Reference}\left(H\right),\; \left(\left(\operatorname{PositiveTraceOne}\left(rho\right) \land \left(\operatorname{PositiveTraceOne}\left(sigma\right) \land \operatorname{Finite}\left(\operatorname{spectralEntropy}\left(rho\right)\right)\right)\right) \land \operatorname{Finite}\left(\operatorname{spectralEnergy}\left(sigma, rho\right)\right)\right) \Rightarrow \operatorname{AllFullResolutionsAbsoluteSignedSumAndZeroFiberFormula}\left(rho, sigma\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/FiniteEntropyRelativeEntropy.finiteEntropyRelativeEntropy_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. E. Shirokov (2012). *On a conjectured property of the von Neumann entropy valid in the commutative case*. URL: <https://arxiv.org/abs/1201.1093v1>.

*Commentary.*

Take arbitrary full resolutions d of rho and e of sigma, including all zero eigenspaces and arbitrary original index sets. At finite cross energy and finite self entropy, the formula is the product-index sum of d(i)*norm(inner(e(j),d(i))) squared times [log(d(i))-log(e(j))]. It is absolutely summable, equals E.toReal-S.toReal, and its ofReal is the actual trace-log divergence. Absolute summability also justifies the iterated signed sum.

The generic extended cross double sum is proved at its original Hellinger source and reused there. Finite total cross energy forces every summand finite. At e(j)=0 this forces d(i)*norm(inner(e(j),d(i))) squared=0 before any singular logarithm is replaced by the real logarithm convention. The nonnegative real cross array sums to E.toReal. Parseval row sums and the arbitrary-resolution entropy identity give a nonnegative self array summing to S.toReal. Finiteness of their ENNReal sums supplies genuine real summability; subtraction and absolute summability precede signed rearrangement. No infinite-energy real tsum interpretation is asserted.

**Theorem 1.5 (One fixed reference from the original family premises).**

$$\forall H \in CompleteComplexHilbertSpace, A \in \operatorname{Set}\left(\operatorname{TraceClass}\left(H\right)\right),\; \operatorname{NonemptyClosedRealConvexPositiveTraceOneFiniteContinuousEntropy}\left(A\right) \Rightarrow \operatorname{CompactAndFixedNormalizedReferenceInFamilyWithFiniteContinuousBoundedActualDivergence}\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/FiniteEntropyRelativeEntropy.closedConvex_finiteEntropy_commonReference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. E. Shirokov (2012). *On a conjectured property of the von Neumann entropy valid in the commutative case*. URL: <https://arxiv.org/abs/1201.1093v1>.

*Commentary.*

Let A be a nonempty trace-norm closed real-convex family of actual positive trace-one operators on H. Assume every actual spectral entropy is finite and realEntropy is continuous on A. The conclusion proves compactness of A and gives an entropy maximizer gamma in A and one normalized reference sigma in A. The actual newly defined divergence to this sigma is finite everywhere, continuous both as an ENNReal function and in its real value on subtype A, bounded above by realEntropy(gamma)+log(2), and bounds the trace-norm square divided by four.

First exists_unique_entropy_maximizer gives a genuine maximum without compactness or an assumed entropy bound. spectralEnergy_le_entropy_of_isMaxOn bounds the entire family by the maximizer's finite self entropy, without a compactness premise. The original closed family is therefore a closed subset of a genuine compact energy sublevel. fullCompactCommonReference then supplies sigma with finite continuous real cross energy. The actual divergence characterization identifies its real value with that energy minus the original realEntropy. Subtraction proves continuity, finite ofReal recovers ENNReal continuity, and nonnegative self entropy gives the uniform upper bound.

Shirokov's original Conjecture 2 supplies the mathematical objective. The result here composes the attributed entropy, jump, compactness and common-reference suppliers with the actual trace-log bridge. The spectral-distribution method and Hellinger bound retain their Nussbaum-Szkola and Physlib attribution. This is a mathematical consequence in the stated formal model; no literature novelty, current openness or all-temperature Hamiltonian claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteEntropyRelativeEntropy.closedConvex_finiteEntropy_commonReference`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteEntropyRelativeEntropy.finiteEntropyRelativeEntropy_branches`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteEntropyRelativeEntropy.finiteEntropyRelativeEntropy_eq_energy_tsub`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteEntropyRelativeEntropy.finiteEntropyRelativeEntropy_spectral`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteEntropyRelativeEntropy.traceLogGrid_operators`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/CompactCommonReference](CompactCommonReference.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/EntropyMaximizer](EntropyMaximizer.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/HellingerEnergy](HellingerEnergy.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/KernelEnergy](KernelEnergy.md)
