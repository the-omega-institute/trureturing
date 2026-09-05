# Explicit-Formula Weil Criterion

## Abstract

Relative to supplied zero data and an explicit archimedean-integrability hypothesis, RH is equivalent to nonnegativity of the classical pole-minus-prime-plus-archimedean expression on every convolution square.

**Theorem 1.1 (The explicit formula for a convolution square).**

$$\begin{aligned}\forall Z \in ZeroData, g \in WeilTestFunction, hArch \in \operatorname{ArchimedeanConvergent}\left(\operatorname{convolutionSquare}\left(g\right)\right),\; \operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(g\right), \operatorname{symmetricConvergentOfZeroData}\left(Z, \operatorname{convolutionSquare}\left(g\right)\right)\right) = \operatorname{poleTerm}\left(\operatorname{convolutionSquare}\left(g\right)\right) - \operatorname{primeTerm}\left(\operatorname{convolutionSquare}\left(g\right)\right) + \operatorname{archimedeanTerm}\left(\operatorname{convolutionSquare}\left(g\right), hArch\right)\\\text{where} \\\operatorname{poleTerm}\left(\operatorname{convolutionSquare}\left(g\right)\right) = \operatorname{fourierLaplace}\left(\operatorname{convolutionSquare}\left(g\right), -\frac{i}{2}\right) + \operatorname{fourierLaplace}\left(\operatorname{convolutionSquare}\left(g\right), \frac{i}{2}\right)\\\operatorname{primeTerm}\left(\operatorname{convolutionSquare}\left(g\right)\right) = \sum_{n \in \mathbb{N}} \frac{\Lambda(n)}{\sqrt{n}} \cdot \left(\operatorname{convolutionSquare}\left(g\right)\left(\log(n)\right) + \operatorname{convolutionSquare}\left(g\right)\left(-\log(n)\right)\right)\\\operatorname{archimedeanTerm}\left(\operatorname{convolutionSquare}\left(g\right), hArch\right) = \frac{1}{2\pi} \cdot \int_{\mathbb{R}} \left(\Re (\psi(\frac{1}{4} + \frac{i \cdot t}{2})) - \operatorname{log}\left(\pi\right)\right) \cdot \operatorname{fourierLaplace}\left(\operatorname{convolutionSquare}\left(g\right), t\right) dt\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/ExplicitFormulaWeilCriterion.explicitFormula_weilSquare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen zeta explicit formula is applied to convolutionSquare(g). The supplied ZeroData gives its canonical symmetric-convergence witness, while hArch is exactly the assumed integrability of the displayed digamma integral; that integrability is not proved here.

The display expands the pole evaluations, the von Mangoldt series Lambda(n)/sqrt(n) times the two logarithmic samples, and the archimedean digamma integral term by term.

**Theorem 1.2 (RH is equivalent to explicit-formula positivity).**

$$\begin{aligned}\forall Z \in ZeroData, hArch \in \left(\forall g \in WeilTestFunction,\; \operatorname{ArchimedeanConvergent}\left(\operatorname{convolutionSquare}\left(g\right)\right)\right),\; \operatorname{RiemannHypothesis} \Leftrightarrow \left(\forall g \in WeilTestFunction,\; 0 \le \Re (\operatorname{poleTerm}\left(\operatorname{convolutionSquare}\left(g\right)\right) - \operatorname{primeTerm}\left(\operatorname{convolutionSquare}\left(g\right)\right) + \operatorname{archimedeanTerm}\left(\operatorname{convolutionSquare}\left(g\right), hArch\left(g\right)\right))\right)\\\text{where} \\\operatorname{poleTerm}\left(\operatorname{convolutionSquare}\left(g\right)\right) = \operatorname{fourierLaplace}\left(\operatorname{convolutionSquare}\left(g\right), -\frac{i}{2}\right) + \operatorname{fourierLaplace}\left(\operatorname{convolutionSquare}\left(g\right), \frac{i}{2}\right)\\\operatorname{primeTerm}\left(\operatorname{convolutionSquare}\left(g\right)\right) = \sum_{n \in \mathbb{N}} \frac{\Lambda(n)}{\sqrt{n}} \cdot \left(\operatorname{convolutionSquare}\left(g\right)\left(\log(n)\right) + \operatorname{convolutionSquare}\left(g\right)\left(-\log(n)\right)\right)\\\operatorname{archimedeanTerm}\left(\operatorname{convolutionSquare}\left(g\right), hArch\left(g\right)\right) = \frac{1}{2\pi} \cdot \int_{\mathbb{R}} \left(\Re (\psi(\frac{1}{4} + \frac{i \cdot t}{2})) - \operatorname{log}\left(\pi\right)\right) \cdot \operatorname{fourierLaplace}\left(\operatorname{convolutionSquare}\left(g\right), t\right) dt\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/ExplicitFormulaWeilCriterion.rh_iff_explicitFormulaPositivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen Weil-square positivity criterion and the preceding explicit formula rewrite each side of the equivalence. Proof irrelevance identifies an arbitrary symmetric-convergence witness with the canonical witness supplied by ZeroData.

The universal hArch premise is explicit: archimedean integrability of every convolution square is assumed, not established in this module. The theorem is relative to a supplied ZeroData; existence of such data is not asserted, and M1-b remains open.

WeilTestFunction here means this repository's even, smooth, compactly supported test functions, not the wider classes used in parts of the literature. This conditional equivalence is not a proof of the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Weil/Separator/ExplicitFormulaWeilCriterion.explicitFormula_weilSquare`
- Truth anchor: `D5/S3/Weil/Separator/ExplicitFormulaWeilCriterion.rh_iff_explicitFormulaPositivity`
- Dependency: [D5/S3/Weil/Separator/WeilSquarePositivityCriterion](WeilSquarePositivityCriterion.md)
- Dependency: [D5/S3/Weil/ZetaBridge/SymmetricConvergentOfZetaSummable](../ZetaBridge/SymmetricConvergentOfZetaSummable.md)
