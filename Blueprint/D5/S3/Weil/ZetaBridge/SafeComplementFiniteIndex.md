# Safe Complement Gap and Finite Negative Index

## Abstract

A concentration-controlled spectral complement has a strict Weil gap and finite negative index.

**Theorem 1.1 (Safe-complement gap).**

$$\forall Z \in \operatorname{ZeroData}\left(\right), L \in \operatorname{Real}\left(\right), a \in \operatorname{Real}\left(\right), eta \in \operatorname{Real}\left(\right), Q \in \operatorname{Function}\left(\operatorname{WeilTestFunction}\left(\right), \operatorname{Prop}\left(\right)\right), f \in \operatorname{WeilTestFunction}\left(\right),\; \left(\operatorname{apply}\left(Q, f\right) \land \left(\operatorname{tsupport}\left(f\right) \subseteq \operatorname{Icc}\left(\operatorname{neg}\left(L\right), L\right) \land \left(\operatorname{SymmetricConvergent}\left(Z, \operatorname{convolutionSquare}\left(f\right)\right) \land \left(\operatorname{ArchimedeanConvergent}\left(\operatorname{convolutionSquare}\left(f\right)\right) \land \left(\operatorname{Integrable}\left(\operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \operatorname{mul}\left(\operatorname{fixedScaleMultiplier}\left(L, xi\right), \operatorname{normSq}\left(\operatorname{fourierLaplace}\left(f, xi\right)\right)\right)\right)\right) \land \left(\operatorname{MeasurableSet}\left(\operatorname{setOf}\left(\operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \operatorname{fixedScaleMultiplier}\left(L, xi\right) < a\right)\right)\right) \land \left(\operatorname{BddBelow}\left(\operatorname{image}\left(\operatorname{fixedScaleMultiplier}\left(L\right), \operatorname{setOf}\left(\operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \operatorname{fixedScaleMultiplier}\left(L, xi\right) < a\right)\right)\right)\right) \land \left(0 < a \land \left(0 < eta \land \left(eta < \operatorname{div}\left(a, \operatorname{add}\left(a, \operatorname{max}\left(0, \operatorname{neg}\left(\operatorname{sInf}\left(\operatorname{image}\left(\operatorname{fixedScaleMultiplier}\left(L\right), \operatorname{setOf}\left(\operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \operatorname{fixedScaleMultiplier}\left(L, xi\right) < a\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall g \in \operatorname{WeilTestFunction}\left(\right),\; \operatorname{apply}\left(Q, g\right) \Rightarrow \operatorname{mul}\left(\operatorname{div}\left(1, \operatorname{mul}\left(2, \operatorname{pi}\left(\right)\right)\right), \operatorname{integralOn}\left(\operatorname{setOf}\left(\operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \operatorname{fixedScaleMultiplier}\left(L, xi\right) < a\right)\right), \operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \operatorname{normSq}\left(\operatorname{fourierLaplace}\left(g, xi\right)\right)\right)\right)\right) \le \operatorname{mul}\left(eta, \operatorname{l2Mass}\left(g\right)\right)\right) \land \left(\forall g \in \operatorname{WeilTestFunction}\left(\right),\; \operatorname{apply}\left(Q, g\right) \Rightarrow \operatorname{integral}\left(\operatorname{Real}\left(\right), \operatorname{lambda}\left(\operatorname{typed}\left(x, \operatorname{Real}\left(\right)\right), \operatorname{mul}\left(\operatorname{cosh}\left(\operatorname{div}\left(x, 2\right)\right), \operatorname{apply}\left(g, x\right)\right)\right)\right) = 0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(0 < \operatorname{sub}\left(a, \operatorname{mul}\left(\operatorname{add}\left(a, \operatorname{max}\left(0, \operatorname{neg}\left(\operatorname{sInf}\left(\operatorname{image}\left(\operatorname{fixedScaleMultiplier}\left(L\right), \operatorname{setOf}\left(\operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \operatorname{fixedScaleMultiplier}\left(L, xi\right) < a\right)\right)\right)\right)\right)\right)\right), eta\right)\right) \land \operatorname{mul}\left(\operatorname{sub}\left(a, \operatorname{mul}\left(\operatorname{add}\left(a, \operatorname{max}\left(0, \operatorname{neg}\left(\operatorname{sInf}\left(\operatorname{image}\left(\operatorname{fixedScaleMultiplier}\left(L\right), \operatorname{setOf}\left(\operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \operatorname{fixedScaleMultiplier}\left(L, xi\right) < a\right)\right)\right)\right)\right)\right)\right), eta\right)\right), \operatorname{l2Mass}\left(f\right)\right) \le \operatorname{realPart}\left(\operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(f\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/SafeComplementFiniteIndex.safe_complement_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the canonical Weil-test carrier, concentration in the dangerous multiplier band and pole orthogonality give the displayed positive gap for the frozen zero-side quadratic form.

**Theorem 1.2 (Finite negative-index bound).**

$$\forall H \in Type, energy \in \operatorname{Function}\left(H, \operatorname{Real}\left(\right)\right), P \in \operatorname{Submodule}\left(\operatorname{Real}\left(\right), H\right), Q \in \operatorname{Submodule}\left(\operatorname{Real}\left(\right), H\right), delta \in \operatorname{Real}\left(\right),\; \left(\operatorname{NormedAddCommGroup}\left(H\right) \land \left(\operatorname{InnerProductSpace}\left(\operatorname{Real}\left(\right), H\right) \land \left(\operatorname{FiniteDimensional}\left(\operatorname{Real}\left(\right), P\right) \land \left(\operatorname{IsCompl}\left(P, Q\right) \land \left(0 < delta \land \left(\forall q \in H,\; q \in Q \Rightarrow \operatorname{mul}\left(delta, \operatorname{pow}\left(\operatorname{norm}\left(q\right), 2\right)\right) \le \operatorname{apply}\left(energy, q\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{negativeIndex}\left(energy\right) \le \operatorname{withTop}\left(\operatorname{finrank}\left(\operatorname{Real}\left(\right), P\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/SafeComplementFiniteIndex.finite_negative_index_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A strictly positive complementary subspace prevents a negative subspace from having dimension larger than the retained summand.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/SafeComplementFiniteIndex.finite_negative_index_bound`
- Truth anchor: `D5/S3/Weil/ZetaBridge/SafeComplementFiniteIndex.safe_complement_gap`
- Dependency: [D5/S3/Weil/ZetaBridge/FixedScaleWeilQuadraticForm](FixedScaleWeilQuadraticForm.md)
- Dependency: [D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition](../ZetaGamma/ArchimedeanJumpDecomposition.md)
- Dependency: [D5/S3/Weil/ZetaLinear/ExactStickyReduction](../ZetaLinear/ExactStickyReduction.md)
