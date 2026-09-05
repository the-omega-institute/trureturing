# Prime-Archimedean Poincare Criterion

## Abstract

Relative to supplied zero data, RH is equivalent to the Prime-Archimedean Poincare inequality at every support radius and at some support radius.

**Theorem 1.1 (RH is equivalent to every-radius Prime-Archimedean Poincare).**

$$\forall Z \in ZeroData,\; \operatorname{RiemannHypothesis} \Leftrightarrow \left(\forall f \in WeilTestFunction, L \in \mathbb{R},\; \operatorname{tsupport}\left(f\right) \subseteq [-L, L] \Rightarrow \left(2 \cdot \operatorname{totalPrimeWeight}\left(L\right) - \operatorname{archimedeanConstant}\right) \cdot \operatorname{l2Mass}\left(f\right) \le 2 \lvert\int_{\mathbb{R}} \operatorname{exp}\left(\frac{x}{2}\right) \operatorname{f}\left(x\right) dx\rvert^{2} + \operatorname{archimedeanJumpEnergy}\left(f\right) + \operatorname{arithmeticJumpEnergy}\left(L, f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/PrimeArchimedeanPoincareCriterion.rh_iff_primeArchimedeanPoincare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The energy decomposition is the frozen theorem PrimeArchimedeanEnergyIdentity proved by another driver and is only bound here; no part of that identity is reproved.

Both criteria are relative to a ZeroData only. Existence of ZeroData is not asserted, M1-b remains open, and these equivalences are not a proof of RH.

The quantified test functions are this repository's WeilTestFunction. The support radius L is any real satisfying tsupport f subset [-L,L]. The existential-radius criterion records that, through the frozen identity, the inequality's truth is independent of which valid radius is chosen.

The left side is the coherent prime mass minus the Archimedean constant, multiplied by the L2 mass. The right side is twice the squared boundary readout plus the Archimedean and arithmetic jump energies.

**Theorem 1.2 (RH is equivalent to existential-radius Prime-Archimedean Poincare).**

$$\forall Z \in ZeroData,\; \operatorname{RiemannHypothesis} \Leftrightarrow \left(\forall f \in WeilTestFunction,\; \exists L \in \mathbb{R},\; \operatorname{tsupport}\left(f\right) \subseteq [-L, L] \land \left(2 \cdot \operatorname{totalPrimeWeight}\left(L\right) - \operatorname{archimedeanConstant}\right) \cdot \operatorname{l2Mass}\left(f\right) \le 2 \lvert\int_{\mathbb{R}} \operatorname{exp}\left(\frac{x}{2}\right) \operatorname{f}\left(x\right) dx\rvert^{2} + \operatorname{archimedeanJumpEnergy}\left(f\right) + \operatorname{arithmeticJumpEnergy}\left(L, f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/PrimeArchimedeanPoincareCriterion.rh_iff_exists_supportRadius_primeArchimedeanPoincare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The energy decomposition is the frozen theorem PrimeArchimedeanEnergyIdentity proved by another driver and is only bound here; no part of that identity is reproved.

Both criteria are relative to a ZeroData only. Existence of ZeroData is not asserted, M1-b remains open, and these equivalences are not a proof of RH.

The quantified test functions are this repository's WeilTestFunction. The support radius L is any real satisfying tsupport f subset [-L,L]. The existential-radius criterion records that, through the frozen identity, the inequality's truth is independent of which valid radius is chosen.

The left side is the coherent prime mass minus the Archimedean constant, multiplied by the L2 mass. The right side is twice the squared boundary readout plus the Archimedean and arithmetic jump energies.

## References

- Truth anchor: `D5/S3/Weil/Separator/PrimeArchimedeanPoincareCriterion.rh_iff_exists_supportRadius_primeArchimedeanPoincare`
- Truth anchor: `D5/S3/Weil/Separator/PrimeArchimedeanPoincareCriterion.rh_iff_primeArchimedeanPoincare`
- Dependency: [D5/S3/Weil/Separator/ArchimedeanConvergence](ArchimedeanConvergence.md)
- Dependency: [D5/S3/Weil/Separator/WeilSquarePositivityCriterion](WeilSquarePositivityCriterion.md)
- Dependency: [D5/S3/Weil/ZetaBridge/PrimeArchimedeanEnergyIdentity](../ZetaBridge/PrimeArchimedeanEnergyIdentity.md)
- Dependency: [D5/S3/Weil/ZetaBridge/SymmetricConvergentOfZetaSummable](../ZetaBridge/SymmetricConvergentOfZetaSummable.md)
