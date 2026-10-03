# Cubic Grover walks and odd periods

## Abstract

No connected 3-regular graph is 2l-periodic for an odd multiple l of 3.

**Definition 1.1 (Grover time evolution matrix).**

$$\forall V: Type [\operatorname{Fintype}\left(V\right)][\operatorname{DecidableEq}\left(V\right)], \forall G: \operatorname{SimpleGraph}\left(V\right) [\operatorname{DecidableRel}\left(G.Adj\right)], \forall a: G.Dart, \forall b: G.Dart, \operatorname{grover}\left(G, a, b\right) = if b.snd = a.fst then \frac{2}{(\operatorname{degree}\left(G, b.snd\right) : \mathbb{C})} - (if a = b.symm then 1 else 0) else 0$$

*Formalization.* `D5/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod.grover` (`✓ std3`).

*Citation.* S. Kubota, H. Sekido and K. Yoshino (2025). *Regular graphs to induce even periodic Grover walks*. DOI: [10.1016/j.disc.2024.114345](https://doi.org/10.1016/j.disc.2024.114345). URL: <https://arxiv.org/abs/2307.13227v1>.

*Commentary.*

Section 2.2 states verbatim: "the time evolution matrix U = U(G) ∈ C^{A×A} of the Grover walk over G is defined by U_{a,b} = 2/deg_G t(b) − 1 if a = b^{−1}; 2/deg_G t(b) if t(b) = o(a) and a ≠ b^{−1}; 0 if t(b) ≠ o(a)." The Lean conditional expression is this three-case definition, with the reversed-arc indicator inside the composability case.

**Definition 1.2 (Minimum period).**

$$\forall n: Type [\operatorname{Fintype}\left(n\right)][\operatorname{DecidableEq}\left(n\right)], \forall U: \operatorname{Matrix}\left(n\right) n \mathbb{C}, \forall \tau: \mathbb{N}, \operatorname{IsPeriodOf}\left(U, \tau\right) \Leftrightarrow (0 < \tau \land \left(U^\tau = 1 \land (\forall \sigma: \mathbb{N}, 0 < \sigma \Rightarrow \left(\sigma < \tau \Rightarrow U^\sigma \ne 1\right))\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod.IsPeriodOf` (`✓ std3`).

*Citation.* S. Kubota, H. Sekido and K. Yoshino (2025). *Regular graphs to induce even periodic Grover walks*. DOI: [10.1016/j.disc.2024.114345](https://doi.org/10.1016/j.disc.2024.114345). URL: <https://arxiv.org/abs/2307.13227v1>.

*Commentary.*

Section 2.2 states verbatim: "If there exists τ ∈ N such that U^τ = I_A, then we say that the graph G is periodic and the minimum τ is period. Such a graph is also called a τ-periodic graph." The definition records positivity, return to the identity, and minimality among positive return times.

**Definition 1.3 (Question 4.11).**

$$\forall l: \mathbb{N}, \operatorname{Odd}\left(l\right) \Rightarrow \left(3 \mid l \Rightarrow \forall V: Type [\operatorname{Fintype}\left(V\right)][\operatorname{DecidableEq}\left(V\right)], \forall G: \operatorname{SimpleGraph}\left(V\right) [\operatorname{DecidableRel}\left(G.Adj\right)], \left(\operatorname{Connected}\left(G\right) \land (\forall v: V, \operatorname{degree}\left(G, v\right) = 3)\right) \Rightarrow \neg \operatorname{IsPeriodOf}\left(\operatorname{grover}\left(G\right), 2 \times l\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod.claim` (`✓ std3`).

*Citation.* S. Kubota, H. Sekido and K. Yoshino (2025). *Regular graphs to induce even periodic Grover walks*. DOI: [10.1016/j.disc.2024.114345](https://doi.org/10.1016/j.disc.2024.114345). URL: <https://arxiv.org/abs/2307.13227v1>.

*Commentary.*

After Theorem 4.10 the source asks verbatim (Question 4.11): "Let l be an odd integer that is a multiple of 3. Do 2l-periodic 3-regular graphs exist?" The encoding uses finite simple connected graphs, degree three at every vertex, and the preceding definition of period.

**Theorem 1.4 (Negative answer to Question 4.11).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Kubota, H. Sekido and K. Yoshino (2025). *Regular graphs to induce even periodic Grover walks*. DOI: [10.1016/j.disc.2024.114345](https://doi.org/10.1016/j.disc.2024.114345). URL: <https://arxiv.org/abs/2307.13227v1>.

*Commentary.*

The integer matrix W=3U has entries 2−3 on a reversed arc and 2 on every other composable transition. Modulo 2 it is the arc-reversal permutation, whose square is the identity. The diagonal of W² is 1. If U^(2l)=I for odd l, the difference-of-powers factor Q is congruent to the identity modulo 2, so its determinant is nonzero; the adjugate identity then forces W²=9I, contradicting the diagonal. Thus U^(2l)≠I for every odd l, which answers Question 4.11.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod.IsPeriodOf`
- Truth anchor: `D5/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod.grover`
- Truth anchor: `D5/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod.result`
