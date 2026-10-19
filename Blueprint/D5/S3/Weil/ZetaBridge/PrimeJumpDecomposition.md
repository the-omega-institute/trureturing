# Prime Jump Decomposition

## Abstract

The finite prime-power term is coherent mass minus a nonnegative translation energy, and that energy is the quadratic form of the arithmetic jump Laplacian.

**Theorem 1.1 (Prime jump decomposition).**

$$\forall f\in \mathcal{W}, L\in \mathbb{R}, hSupport: \operatorname{tsupport}\left(f\right) \subseteq [-L, L] \Rightarrow \operatorname{primeTerm}\left(\operatorname{convolutionSquare}\left(f\right)\right) = 2 \cdot \operatorname{totalPrimeWeight}\left(L\right) \cdot \operatorname{l2Mass}\left(f\right) - \operatorname{arithmeticJumpEnergy}\left(L, f\right) \land \left(0 \le \operatorname{arithmeticJumpEnergy}\left(L, f\right) \land \operatorname{arithmeticJumpEnergy}\left(L, f\right) = \Re(\int_{\mathbb{R}} \operatorname{conj}\left(\operatorname{f}\left(y\right)\right) \cdot \operatorname{arithmeticJumpLaplacian}\left(L, f, y\right) dy)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeJumpDecomposition.prime_jump_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The test function lies in the canonical carrier of even smooth compactly supported complex-valued functions. The displayed support witness places its support inside the interval from minus L to L.

The active channels are the prime powers at or below exp(2L), filtered by nonzero von Mangoldt weight. Their critical-line weights are summed to form the coherent mass and weight the squared translation displacements in the arithmetic energy.

For the concrete same-window L2 application documented with WeilMellinPrimeIntertwining.primeSymmetric, use this source's activePrimePowers, primeWeight and totalPrimeWeight unchanged. With P_L the actual interval-indicator projection and T_s=P_L U_s P_L, the corresponding bounded unsigned block is sum_n primeWeight(n)*(T_log(n)+T_{-log(n)}). Its norm is at most 2*totalPrimeWeight(L), because both compressed translations are contractions and every weight is nonnegative. Its exact finite representative retains every prime power and agrees almost everywhere with the existing primeSymmetric at cutoff floor(exp(2L)). The equality channel log(n)=2L is the zero compressed operator, while the definition of totalPrimeWeight still includes that channel's weight. The displayed arithmeticJumpLaplacian keeps its original full-space pointwise definition and smooth even test-function hypotheses.

All three source clauses are public: the exact complex prime-term decomposition, nonnegativity of the independently constructed energy, and its equality with the real part of the explicit Laplacian quadratic form.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeJumpDecomposition.prime_jump_decomposition`
- Dependency: [D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition](../ZetaGamma/ArchimedeanJumpDecomposition.md)
