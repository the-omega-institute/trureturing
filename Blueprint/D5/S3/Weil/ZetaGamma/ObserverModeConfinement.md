# Observer-Mode Confinement

## Abstract

Proper joint growth of the completed-zeta Archimedean mode confines every bounded-prime strict sublevel in both observer mode and frequency.

**Theorem 1.1 (Finite dangerous modes and a common frequency window).**

$$\begin{aligned}\forall primeMultiplier \in \mathbb{R} \to \left(\mathbb{Z} \to \left(\mathbb{R} \to \mathbb{R}\right)\right), L \in \mathbb{R}, A \in \mathbb{R}, B \in \mathbb{R},\; \left(\forall n \in \mathbb{Z}, t \in \mathbb{R},\; \left\lVert primeMultiplier\left(L, n, t\right) \right\rVert \le B\right) \Rightarrow \operatorname{let} modeShift: \mathbb{Z} \to \mathbb{R} = n: \mathbb{Z} \mapsto n \cdot goldenAngularFrequency, \operatorname{let} archimedeanMode: \mathbb{Z} \times \mathbb{R} \to \mathbb{R} = nt: \mathbb{Z} \times \mathbb{R} \mapsto \frac{1}{2} \cdot \left(2 \cdot \pi \cdot \operatorname{mu}\left(\operatorname{snd}\left(nt\right) + modeShift\left(\operatorname{fst}\left(nt\right)\right)\right) + 2 \cdot \pi \cdot \operatorname{mu}\left(\operatorname{snd}\left(nt\right) - modeShift\left(\operatorname{fst}\left(nt\right)\right)\right)\right), \operatorname{Tendsto}\left(archimedeanMode, \operatorname{cocompact}\left(\mathbb{Z} \times \mathbb{R}\right), atTop\right) \Rightarrow \operatorname{let} jointMultiplier: \mathbb{Z} \times \mathbb{R} \to \mathbb{R} = nt: \mathbb{Z} \times \mathbb{R} \mapsto archimedeanMode\left(nt\right) - primeMultiplier\left(L, \operatorname{fst}\left(nt\right), \operatorname{snd}\left(nt\right)\right), \operatorname{let} dangerousSet: \operatorname{Set}\left(\mathbb{Z} \times \mathbb{R}\right) = \{nt \in \mathbb{Z} \times \mathbb{R} \mid jointMultiplier\left(nt\right) < A\}, \operatorname{Finite}\left(\{n \in \mathbb{Z} \mid \exists t \in \mathbb{R},\; (n, t) \in dangerousSet\}\right) \land \left(\left(\forall n \in \mathbb{Z},\; \operatorname{IsBounded}\left(\{t \in \mathbb{R} \mid (n, t) \in dangerousSet\}\right)\right) \land \left(\exists modes \in \operatorname{Finset}\left(\mathbb{Z}\right), radius \in \mathbb{R},\; 0 \le radius \land \left(\forall n \in \mathbb{Z}, t \in \mathbb{R},\; jointMultiplier\left((n, t)\right) < 0 \Rightarrow \left(n \in modes \land \left\lVert t \right\rVert \le radius\right)\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/ObserverModeConfinement.two_direction_archimedean_confinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observer shift is the canonical integer multiple of the golden angular frequency. The Archimedean term is the symmetric average of the existing completed-zeta digamma multiplier 2 pi mu.

The public hypotheses state proper growth on the full integer-by-real carrier and a uniform bound for the fixed-support prime multiplier. No mode or frequency is specialized.

A compact complement of a sufficiently high Archimedean superlevel contains both the threshold danger set and the negativity set. Its integer projection is finite, while its real projection is bounded.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/ObserverModeConfinement.two_direction_archimedean_confinement`
- Dependency: [D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling](../../Observer/GoldenPrimeCircle/GoldenVerticalSampling.md)
