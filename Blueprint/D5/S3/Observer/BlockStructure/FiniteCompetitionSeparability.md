# Finite Competition Separability

## Abstract

Finite symmetric competitors admit a positive common-denominator feature margin.

**Theorem 1.1 (Finite character depth separates every finite competitor family).**

$$\begin{aligned}\forall q: \mathbb{N}, m: \mathbb{N},\\r: \operatorname{Fin}\left(q\right) \to \mathbb{R}, N: \operatorname{Fin}\left(q\right) \to \mathbb{N},\\scaleInDisk: \forall i \in \operatorname{Fin}\left(q\right),\; \operatorname{abs}\left(r\left(i\right)\right) < 1,\\z: \operatorname{Fin}\left(m + 1\right) \to \mathbb{C},\\orbitDistinct: \forall i \in \operatorname{Fin}\left(m + 1\right), j \in \operatorname{Fin}\left(m + 1\right),\; i \ne j \Rightarrow \left(z\left(i\right) \ne z\left(j\right) \land \left(z\left(i\right) \ne \operatorname{neg}\left(z\left(j\right)\right) \land \left(z\left(i\right) \ne \operatorname{conj}\left(z\left(j\right)\right) \land z\left(i\right) \ne \operatorname{neg}\left(\operatorname{conj}\left(z\left(j\right)\right)\right)\right)\right)\right),\\noPole: \forall j \in \operatorname{Fin}\left(m + 1\right),\; \operatorname{eval}\left(\operatorname{prod}\left(\operatorname{Fin}\left(q\right), (i: \operatorname{Fin}\left(q\right) \mapsto \operatorname{pow}\left(1 + \operatorname{C}\left(\operatorname{ofReal}\left(r\left(i\right)\right)\right) \cdot X, N\left(i\right) + 1\right))\right), z\left(j\right)\right) \ne 0,\\\exists d \in \mathbb{N},\; \operatorname{let}(f: \operatorname{Fin}\left(q\right) \to \operatorname{Polynomial}\left(\mathbb{C}\right), \forall i: \operatorname{Fin}\left(q\right), f\left(i\right) = 1 + \operatorname{C}\left(\operatorname{ofReal}\left(r\left(i\right)\right)\right) \cdot X\;D: \operatorname{Polynomial}\left(\mathbb{C}\right) = \operatorname{prod}\left(\operatorname{Fin}\left(q\right), (i: \operatorname{Fin}\left(q\right) \mapsto \operatorname{pow}\left(f\left(i\right), N\left(i\right) + 1\right))\right)\;p: \operatorname{Fin}\left(d + 1\right) \to \operatorname{Polynomial}\left(\mathbb{C}\right), \forall k: \operatorname{Fin}\left(d + 1\right), p\left(k\right) = D \cdot \operatorname{pow}\left(X, 2 \cdot k\right)\;\phi: \mathbb{C} \to \left(\operatorname{Fin}\left(d + 1\right) \to \mathbb{C}\right), \forall w: \mathbb{C}, k: \operatorname{Fin}\left(d + 1\right), \phi\left(w\right)\left(k\right) = \frac{\operatorname{eval}\left(p\left(k\right), w\right)}{\operatorname{eval}\left(D, w\right)}\;W: \operatorname{Submodule}\left(\mathbb{R}, \operatorname{Fin}\left(d + 1\right) \to \mathbb{C}\right) = \operatorname{span}\left(\mathbb{R}, \operatorname{range}\left((j: \operatorname{Fin}\left(m\right) \mapsto \phi\left(z\left(\operatorname{succ}\left(j\right)\right)\right))\right)\right)), \left(\forall w \in \mathbb{C},\; \operatorname{norm}\left(w\right) = 1 \Rightarrow \operatorname{eval}\left(D, w\right) \ne 0\right) \land 0 < \operatorname{infDist}\left(\phi\left(z\left(0\right)\right), W\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/FiniteCompetitionSeparability.finite_competition_separability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scale family, every external depth, and the finite orbit family are public inputs. The sign and conjugation exclusions state the orbit quotient directly, without introducing a proxy quotient.

The supplied scales construct the common denominator. Its disk bounds exclude unit-circle poles, while the finite-point premise keeps each displayed rational profile defined at every competitor.

An even polynomial with every competing orbit as a root gives a real-linear functional that vanishes on the competitor span but not on the target profile. Closedness of the finite span then makes the displayed distance strictly positive.

## References

- Truth anchor: `D5/S3/Observer/BlockStructure/FiniteCompetitionSeparability.finite_competition_separability`
- Dependency: [D5/S3/Observer/BlockStructure/CommonDenominatorPolynomialBasis](CommonDenominatorPolynomialBasis.md)
