# The complete actual Gamma difference keeps a finite signed resonance

## Abstract

The same-source graph closure and convergent series yield the literal Gamma identity.

**Theorem 1.1 (The actual shifted Gamma graph is the bare-quarter graph).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/SourceActualGammaCross.shifted_actual_gamma_graph_equivalence`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/SourceActualGammaCross.shifted_actual_gamma_graph_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each actual whole-line L1 and L2 input and every real constant shift c, integrability of (gammaWeight+c)*abs(Fourier)^2 is equivalent to the original W graph. The actual rational factor (xi^2+1/16)/(xi^2+25/16) lies between 1/25 and 1; the remaining multiplier is bounded. Unweighted Plancherel pays the bounded remainder. The argument handles negative shifts using absolute integrability.

**Theorem 1.2 (The complete positive tail and remaining mixed moment).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/SourceActualGammaCross.actual_gamma_literal_even_difference_positive_tail_and_resonance`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/SourceActualGammaCross.actual_gamma_literal_even_difference_positive_tail_and_resonance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let u be the original arbitrary complex half-line L1 and L2 input, and assume precisely its original zero-extension shifted-Gamma graph. The literal even function u(abs(t)) has an actual shifted-Gamma graph, and the positive tail is summable. With L_a=integral(t>0,exp(-a*t)*u(t)) and T_a=integral(t>0,t*exp(-a*t)*u(t)), the exact identity is sqrt(pi)*(E_Gamma(zero(u))-E_Gamma(even(u))/2) = sum(n>=0,(1+3/[2*(n+1)*(n+7/2)])*normSq(L_(n+9/4))) + A*normSq(L_(5/4))-(6/5)*Re(conj(L_(5/4))*T_(5/4)), where A=64/25+(6/5)*(Re(psi(1))-log(2*pi)). The complete quarter-pole contribution cancels after summability and the scalar digamma-gap identity are proved. The 5/4 mixed moment remains. This is a signed energy identity; subsequent original-source physical estimates are needed for a lower bound, and no RH conclusion is asserted.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/SourceActualGammaCross.actual_gamma_literal_even_difference_positive_tail_and_resonance`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/SourceActualGammaCross.shifted_actual_gamma_graph_equivalence`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample](ActualSuzukiDomainCounterexample.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/SourceGammaResidualCross](SourceGammaResidualCross.md)
