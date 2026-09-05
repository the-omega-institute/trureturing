# Unconditional Explicit Formula

## Abstract

The classical explicit formula and prime-archimedean energy identity hold for every repository Weil test function without separate convergence hypotheses, and below the first prime power the Poincare target reduces to its archimedean part.

The explicit formula and the energy decomposition are frozen theorems of this repository; the latter was supplied by another driver. They are only de-hypothesized here through the frozen W-12 archimedean convergence theorem and the frozen M2-c symmetric convergence theorem.

The analytic identities are relative to supplied ZeroData only. Existence of ZeroData is not asserted, and M1-b remains open. Every test function below is this repository's WeilTestFunction.

The small-support theorem is only a reduction: it does not assert the reduced archimedean inequality, which remains the open target of the ZetaGamma line. None of these statements is a proof of the Riemann hypothesis.

**Theorem 1.1 (The explicit formula without convergence hypotheses).**

$$\forall Z \in ZeroData, g \in WeilTestFunction,\; \operatorname{zeroSum}\left(Z, g, \operatorname{symmetricConvergentOfZeroData}\left(Z, g\right)\right) = \operatorname{poleTerm}\left(g\right) - \operatorname{primeTerm}\left(g\right) + \operatorname{archimedeanTerm}\left(g, \operatorname{archimedeanConvergentOfWeilTestFunction}\left(g\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/UnconditionalExplicitFormula.explicitFormula_unconditional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The symmetric and archimedean convergence arguments are the canonical witnesses supplied by M2-c and W-12, respectively.

**Theorem 1.2 (The prime-archimedean energy identity without convergence hypotheses).**

$$\forall Z \in ZeroData, f \in WeilTestFunction, L \in \mathbb{R}, hSupport \in \operatorname{tsupport}\left(f\right) \subseteq [-L, L],\; \operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(f\right), \operatorname{symmetricConvergentOfZeroData}\left(Z, \operatorname{convolutionSquare}\left(f\right)\right)\right) = 2 \cdot \operatorname{normSq}\left(\int_{\mathbb{R}} \operatorname{exp}\left(\frac{x}{2}\right) \cdot \operatorname{f}\left(x\right) dx\right) + \operatorname{archimedeanJumpEnergy}\left(f\right) + \operatorname{arithmeticJumpEnergy}\left(L, f\right) - \left(2 \cdot \operatorname{totalPrimeWeight}\left(L\right) - \operatorname{archimedeanConstant}\right) \cdot \operatorname{l2Mass}\left(f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/UnconditionalExplicitFormula.energyIdentity_unconditional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support hypothesis is unchanged. Only the two convergence premises of the frozen decomposition are discharged.

**Theorem 1.3 (Small support removes the arithmetic prime-power energy).**

$$\forall f \in WeilTestFunction, L \in \mathbb{R}, hL \in \operatorname{exp}\left(2 \cdot L\right) < 2,\; \left(2 \cdot \operatorname{totalPrimeWeight}\left(L\right) - \operatorname{archimedeanConstant}\right) \cdot \operatorname{l2Mass}\left(f\right) \le 2 \cdot \operatorname{normSq}\left(\int_{\mathbb{R}} \operatorname{exp}\left(\frac{x}{2}\right) \cdot \operatorname{f}\left(x\right) dx\right) + \operatorname{archimedeanJumpEnergy}\left(f\right) + \operatorname{arithmeticJumpEnergy}\left(L, f\right) \Leftrightarrow -\operatorname{archimedeanConstant} \cdot \operatorname{l2Mass}\left(f\right) \le 2 \cdot \operatorname{normSq}\left(\int_{\mathbb{R}} \operatorname{exp}\left(\frac{x}{2}\right) \cdot \operatorname{f}\left(x\right) dx\right) + \operatorname{archimedeanJumpEnergy}\left(f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/UnconditionalExplicitFormula.smallSupport_poincare_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strict threshold exp(2L) < 2 makes activePrimePowers(L) empty, so both totalPrimeWeight(L) and arithmeticJumpEnergy(L,f) vanish.

## References

- Truth anchor: `D5/S3/Weil/Separator/UnconditionalExplicitFormula.energyIdentity_unconditional`
- Truth anchor: `D5/S3/Weil/Separator/UnconditionalExplicitFormula.explicitFormula_unconditional`
- Truth anchor: `D5/S3/Weil/Separator/UnconditionalExplicitFormula.smallSupport_poincare_reduction`
- Dependency: [D5/S3/Weil/Separator/ArchimedeanConvergence](ArchimedeanConvergence.md)
- Dependency: [D5/S3/Weil/ZetaBridge/PrimeArchimedeanEnergyIdentity](../ZetaBridge/PrimeArchimedeanEnergyIdentity.md)
- Dependency: [D5/S3/Weil/ZetaBridge/SymmetricConvergentOfZetaSummable](../ZetaBridge/SymmetricConvergentOfZetaSummable.md)
