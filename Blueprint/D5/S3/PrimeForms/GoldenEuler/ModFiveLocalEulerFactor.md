# Mod-Five Local Euler Factor

## Abstract

The mod-five local observer determinant splits into its even and odd channel factors.

**Theorem 1.1 (The two canonical observer channels give the two local factors).**

$$\forall p \in Nat.Primes, x \in \operatorname{Complex}\left(\right), s \in \operatorname{Complex}\left(\right),\; \operatorname{let} chi: \operatorname{Complex}\left(\right) = \operatorname{cast}\left(\operatorname{Complex}\left(\right), \operatorname{legendreSym}\left(5, p\right)\right), \operatorname{let} localObserverOperator: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \operatorname{Complex}\left(\right)\right) = \operatorname{goldenLocalBranchOperator}\left(p\right), \operatorname{let} primeScale: \operatorname{Complex}\left(\right) = \operatorname{cast}\left(\operatorname{Complex}\left(\right), p\right)^{-s}, \operatorname{inverse}\left(\operatorname{det}\left(\operatorname{identityMatrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Complex}\left(\right)\right) - \operatorname{smul}\left(x, localObserverOperator\right)\right)\right) = \frac{1}{\left(1 - x\right) \cdot \left(1 - chi \cdot x\right)} \land \left(\operatorname{inverse}\left(\operatorname{det}\left(\operatorname{identityMatrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Complex}\left(\right)\right) - \operatorname{smul}\left(primeScale, localObserverOperator\right)\right)\right) = \operatorname{inverse}\left(1 - primeScale\right) \cdot \operatorname{inverse}\left(1 - chi \cdot primeScale\right) \land \left(\operatorname{IsCompl}\left(evenChannel, oddChannel\right) \land \left(\left(\forall value \in \operatorname{BranchSpace}\left(\right),\; \operatorname{mem}\left(value, evenChannel\right) \Rightarrow \operatorname{mulVec}\left(localObserverOperator, value\right) = value\right) \land \left(\forall value \in \operatorname{BranchSpace}\left(\right),\; \operatorname{mem}\left(value, oddChannel\right) \Rightarrow \operatorname{mulVec}\left(localObserverOperator, value\right) = \operatorname{smul}\left(chi, value\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/ModFiveLocalEulerFactor.mod_five_local_observer_determinant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported golden local branch operator is the canonical sum of the even projection and the quadratic-character-weighted odd projection. No second operator definition is introduced here.

Its generic inverse determinant is the product denominator. Substituting the prime scale gives the Riemann and quadratic Dirichlet local factors.

The imported even and odd channels are complementary. The same operator acts by one on every even-channel vector and by the mod-five character on every odd-channel vector, so their one-dimensional inverse determinants are the displayed factors.

## References

- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/ModFiveLocalEulerFactor.mod_five_local_observer_determinant`
- Dependency: [D5/S3/Observer/GoldenCoding/GoldenBranchObserverDecomposition](../../Observer/GoldenCoding/GoldenBranchObserverDecomposition.md)
