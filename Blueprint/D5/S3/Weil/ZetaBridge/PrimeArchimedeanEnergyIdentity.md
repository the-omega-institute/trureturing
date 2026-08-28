# Prime-Archimedean Energy Identity

## Abstract

The zero-side Weil form is boundary energy plus continuous and arithmetic jump energies minus the coherent mass threshold.

**Theorem 1.1 (Prime-Archimedean energy identity).**

$$\forall Z: \operatorname{ZeroData}, f\in \mathcal{W}, L\in \mathbb{R}, hSupport: \operatorname{tsupport}\left(f\right) \subseteq [-L, L], hZero: \operatorname{SymmetricConvergent}\left(Z, \operatorname{convolutionSquare}\left(f\right)\right), hArch: \operatorname{ArchimedeanConvergent}\left(\operatorname{convolutionSquare}\left(f\right)\right) \Rightarrow \operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(f\right), hZero\right) = 2 \lvert\int_{\mathbb{R}} \operatorname{exp}\left(\frac{x}{2}\right) \operatorname{f}\left(x\right) dx\rvert^{2} + \operatorname{archimedeanJumpEnergy}\left(f\right) + \operatorname{arithmeticJumpEnergy}\left(L, f\right) - \left(2 \cdot \operatorname{totalPrimeWeight}\left(L\right) - \operatorname{archimedeanConstant}\right) \cdot \operatorname{l2Mass}\left(f\right) \land \left(0 \le \Re(\operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(f\right), hZero\right)) \Leftrightarrow \left(2 \cdot \operatorname{totalPrimeWeight}\left(L\right) - \operatorname{archimedeanConstant}\right) \cdot \operatorname{l2Mass}\left(f\right) \le 2 \lvert\int_{\mathbb{R}} \operatorname{exp}\left(\frac{x}{2}\right) \operatorname{f}\left(x\right) dx\rvert^{2} + \operatorname{archimedeanJumpEnergy}\left(f\right) + \operatorname{arithmeticJumpEnergy}\left(L, f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeArchimedeanEnergyIdentity.prime_archimedean_energy_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Z is the frozen multiplicity-aware nontrivial-zero enumeration, while f is an even smooth compactly supported complex test function. The support, symmetric zero convergence, and Archimedean convergence witnesses are exactly those consumed by the explicit formula.

The boundary term is twice the squared modulus of the one-half Fourier-Laplace observation. The remaining positive terms are the canonical continuous Archimedean jump energy and the finite prime-power translation energy.

The first public conjunct is the exact complex zero-side identity. The second states that zero-side nonnegativity is equivalent to the displayed Prime-Archimedean Poincare inequality.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeArchimedeanEnergyIdentity.prime_archimedean_energy_identity`
- Dependency: [D5/S3/Weil/ZetaBridge/PoleRankOneDecomposition](PoleRankOneDecomposition.md)
- Dependency: [D5/S3/Weil/ZetaBridge/PrimeJumpDecomposition](PrimeJumpDecomposition.md)
