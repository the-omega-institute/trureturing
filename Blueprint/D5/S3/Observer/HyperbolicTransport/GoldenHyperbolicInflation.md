# Golden Visible-Hidden Hyperbolic Transport

## Abstract

Golden inflation expands the visible face and contracts the conjugate residual.

**Theorem 1.1 (Golden visible-hidden hyperbolic transport).**

$$\forall Phi, P_{parallel}, P_{\perp} \in \operatorname{End}_{\mathbb{R}}(\mathbb{R}^{6}),\ Phi \circ P_{parallel} = \varphi \cdot P_{parallel} \land Phi \circ P_{\perp} = \varphi' \cdot P_{\perp} \land P_{parallel} \circ P_{parallel} = P_{parallel} \land P_{\perp} \circ P_{\perp} = P_{\perp} \land P_{parallel} \circ P_{\perp} = 0 \land P_{parallel} + P_{\perp} = I \land P_{parallel} \circ Phi = Phi \circ P_{parallel} \land P_{\perp} \circ Phi = Phi \circ P_{\perp} \land \operatorname{finrank}\left(\operatorname{range}\left(P_{parallel}\right)\right) = 3 \land \operatorname{finrank}\left(\operatorname{range}\left(P_{\perp}\right)\right) = 3 \Rightarrow \forall n \in \mathbb{N},\ \forall x \in \mathbb{R}^{6},\ P_{parallel}(Phi^{n}(x)) = \varphi^{n} \cdot P_{parallel}(x) \land \left(P_{\perp}(Phi^{n}(x)) = \varphi'^{n} \cdot P_{\perp}(x) \land \left(epsilon_{n} = \varphi^{-n} \land \left(epsilon_{n} = \left|\varphi'\right|^{n} \land \left(0 < epsilon_{1} \land epsilon_{1} < 1\right)\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HyperbolicTransport/GoldenHyperbolicInflation.golden_visible_hidden_hyperbolic_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ambient carrier is the source six-dimensional real space. Phi, P_parallel, and P_perp are supplied operators: the two projections are complementary, commute with Phi, have rank-three images, and satisfy the stated expanding and contracting spectral equations.

Writing q_parallel and q_perp for the two projection readouts, induction on n proves that q_parallel(Phi^n x) and q_perp(Phi^n x) acquire the factors phi^n and (phi-prime)^n. The transport law is therefore a consequence of the hypotheses on the given Phi, not the reduction of a coordinatewise-defined inflation function.

FibonacciEigen supplies contracting_eigenvalue_eq_goldenConj. Together with the pinned real golden-ratio identities, it identifies epsilon_n with both phi^(-n) and |phi-prime|^n and proves that the one-step scale lies strictly between zero and one.

## References

- Truth anchor: `D5/S3/Observer/HyperbolicTransport/GoldenHyperbolicInflation.golden_visible_hidden_hyperbolic_transport`
- Dependency: [D5/S1/Scale/FibonacciEigen](../../../S1/Scale/FibonacciEigen.md)
