# The mixed-memory hierarchy is not complete

## Abstract

An asymmetric five-pattern mixed memory for quadratic activation lies outside the composition hierarchy. Exact correlations on the five-dimensional cube and the strong law yield its limiting overlaps.

**Definition 1.1 (Allowable compositions).**

$$\forall n : \mathbb{N}, \forall c : \operatorname{Composition}\left(n\right), (\operatorname{allowable}\left(c\right)) \Leftrightarrow (((\neg c.\operatorname{blocks} = []) \land (\forall a : \mathbb{N}, (a \in \operatorname{List}.\operatorname{dropLast}\left(c.\operatorname{blocks}\right)) \Rightarrow ((2 \le a) \land (\operatorname{Even}\left(a\right))))) \land (\operatorname{Odd}\left(\operatorname{List}.\operatorname{getLastD}\left(c.\operatorname{blocks}, 0\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.allowable` (`✓ std3`).

*Citation.* Véronique Gayrard (2025). *Mixed memories in Hopfield networks*. URL: <https://arxiv.org/abs/2504.04879v2>.

*Commentary.*

Printed p. 5: "We call an $\ell$-composition ($n_{1}$,…,$n_{\ell}$) allowable if $n_{k} \ge 2$ is even for all $1 \leq k \leq \ell - 1$ and $n_{\ell} \ge 1$ is odd." Mathlib Composition(n) is a list of strictly positive natural blocks summing to n. dropLast removes the last block; getLastD selects it, using zero only for an empty list. Nonemptiness excludes the empty composition. Indices are zero-based.

**Definition 1.2 (Products along a composition).**

$$\forall n : \mathbb{N}, \forall c : \operatorname{Composition}\left(n\right), \forall k : \operatorname{Fin}\left(c.\operatorname{length}\right), \operatorname{gamma}\left(c, k\right) = \operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{map}\left(PrecessionSpinOneSeparableBound.c, \operatorname{List}.\operatorname{take}\left(\operatorname{val}\left(k\right) + 1, c.\operatorname{blocks}\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.gamma` (`✓ std3`).

*Citation.* Véronique Gayrard (2025). *Mixed memories in Hopfield networks*. URL: <https://arxiv.org/abs/2504.04879v2>.

*Commentary.*

For every positive block size a, PrecessionSpinOneSeparableBound.c(a) is the source's α^(a) = 2^(-a+1) binom(a-1,floor((a-1)/2)), reused from D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound; the source's (1.2.1.5), printed (1.10), p. 5, defines gamma(k) as the product of these factors in the first k blocks. Fin indices begin at zero, so gamma(c,k) takes k.val+1 blocks.

**Definition 1.3 (The strict hierarchy inequalities).**

$$\forall n : \mathbb{N}, \forall F : (\mathbb{R}) \to (\mathbb{R}), \forall c : \operatorname{Composition}\left(n\right), (\operatorname{hierarchySystem}\left(F, c\right)) \Leftrightarrow (\forall k : \operatorname{Fin}\left(c.\operatorname{length}\right), (\operatorname{val}\left(k\right) + 1 < c.\operatorname{length}) \Rightarrow (2 \cdot \operatorname{deriv}\left(F, \operatorname{gamma}\left(c, k\right)\right) > \sum_{r:\operatorname{Fin}\left(c.\operatorname{length}\right)} \operatorname{if} (k < r) \operatorname{then} (c.\operatorname{blocksFun}\left(r\right):\mathbb{R}) \cdot \operatorname{deriv}\left(F, \operatorname{gamma}\left(c, r\right)\right) \operatorname{else} 0))$$

*Formalization.* `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.hierarchySystem` (`✓ std3`).

*Citation.* Véronique Gayrard (2025). *Mixed memories in Hopfield networks*. URL: <https://arxiv.org/abs/2504.04879v2>.

*Commentary.*

The source's system S, (1.2.1.12bis), printed (1.13), p. 5: for each nonfinal block, twice the derivative at its gamma value exceeds the sum of all later block lengths times the derivatives at their gamma values. The last block imposes no inequality.

**Definition 1.4 (The padded block vector).**

$$\forall n : \mathbb{N}, \forall c : \operatorname{Composition}\left(n\right), \forall mu : \mathbb{N}, \operatorname{blockVector}\left(c, mu\right) = \operatorname{if} h:mu < n \operatorname{then} \operatorname{gamma}\left(c, c.\operatorname{index}\left(\operatorname{Fin}.\operatorname{mk}\left(mu, h\right)\right)\right) \operatorname{else} 0$$

*Formalization.* `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.blockVector` (`✓ std3`).

*Citation.* Véronique Gayrard (2025). *Mixed memories in Hopfield networks*. URL: <https://arxiv.org/abs/2504.04879v2>.

*Commentary.*

Printed p. 5: "Given $\gamma_{n} \in \mathcal{G}_{n,F}$, let $m(\gamma_{n}) = (m_{\mu}(\gamma_{n}))_{1 \leq \mu \leq M}$ be the vector whose components are constant and equal to $\gamma^{(k)}$ on consecutive blocks of length $n_{k}$, $1 \leq k \leq \ell$, and are $0$ beyond," as displayed in (1.2.1.8), printed (1.14). Composition.index selects the unique block containing the zero-based coordinate mu; the dependent Fin constructor contains its bound proof h.

**Definition 1.5 (The literal coefficient set).**

$$\forall n : \mathbb{N}, \forall F : (\mathbb{R}) \to (\mathbb{R}), \forall M : \mathbb{N}, \forall m : (\operatorname{Fin}\left(M\right)) \to (\mathbb{R}), (m \in \operatorname{coefficientSet}\left(n, F, M\right)) \Leftrightarrow (\exists c : \operatorname{Composition}\left(n\right), ((\operatorname{allowable}\left(c\right)) \land (\operatorname{hierarchySystem}\left(F, c\right))) \land (\exists pi : \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(M\right)\right), \exists eps : (\operatorname{Fin}\left(M\right)) \to (\mathbb{R}), (\forall mu : \operatorname{Fin}\left(M\right), (eps\left(mu\right) = -1) \lor (eps\left(mu\right) = 1)) \land (\forall mu : \operatorname{Fin}\left(M\right), m\left(mu\right) = eps\left(mu\right)^{\operatorname{if} (\forall x : \mathbb{R}, \operatorname{deriv}\left(F, -x\right) = -\operatorname{deriv}\left(F, x\right)) \operatorname{then} 1 \operatorname{else} 2} \cdot \operatorname{blockVector}\left(c, \operatorname{val}\left(pi\left(mu\right)\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.coefficientSet` (`✓ std3`).

*Citation.* Véronique Gayrard (2025). *Mixed memories in Hopfield networks*. URL: <https://arxiv.org/abs/2504.04879v2>.

*Commentary.*

The source's (1.2.1.15), printed (1.15), p. 6, takes all allowable compositions satisfying S, all permutations of the M coordinates, and all coordinate signs. The sign exponent is 1 if the derivative is odd and 2 otherwise. Here coefficientSet(n,F,M) is a Set of functions Fin(M) → R.

**Definition 1.6 (The mixed configuration).**

$$\forall Omega : \operatorname{Type}, \forall F : (\mathbb{R}) \to (\mathbb{R}), \forall M : (\mathbb{N}) \to (\mathbb{N}), \forall m : (\mathbb{N}) \to (\mathbb{R}), \forall xi : (\mathbb{N}) \to ((\mathbb{N}) \to ((Omega) \to (\mathbb{R}))), \forall N : \mathbb{N}, \forall i : \mathbb{N}, \forall omega : Omega, \operatorname{memorySpin}\left(F, M, m, xi, N, i, omega\right) = \operatorname{Real}.\operatorname{sign}\left(\sum_{mu \in \operatorname{Finset}.\operatorname{range}\left(M\left(N\right)\right)} xi\left(mu, i, omega\right) \cdot \operatorname{deriv}\left(F, m\left(mu\right)\right) \cdot \operatorname{if} (\neg m\left(mu\right) = 0) \operatorname{then} 1 \operatorname{else} 0\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.memorySpin` (`✓ std3`).

*Citation.* Véronique Gayrard (2025). *Mixed memories in Hopfield networks*. URL: <https://arxiv.org/abs/2504.04879v2>.

*Commentary.*

Definition 1.1, p. 4, defines xi_i(m) = sign(sum_mu xi_i^mu F'(m_mu) 1_{m_mu ≠ 0}). The pattern and site indices are shifted by one: Lean mu and i correspond to source mu+1 and i+1. The source's sign convention (2.2.2), printed (2.25), p. 15, is +1 above zero, -1 below zero, and 0 at zero; Real.sign has precisely this convention. M(N) permits the number of patterns to vary with N.

**Definition 1.7 (Mixed memories of type F).**

$$\forall Omega : \operatorname{Type}, [\operatorname{MeasurableSpace}\left(Omega\right)] \forall P : \operatorname{Measure}\left(Omega\right), \forall n : \mathbb{N}, \forall F : (\mathbb{R}) \to (\mathbb{R}), \forall M : (\mathbb{N}) \to (\mathbb{N}), \forall m : (\mathbb{N}) \to (\mathbb{R}), \forall xi : (\mathbb{N}) \to ((\mathbb{N}) \to ((Omega) \to (\mathbb{R}))), (\operatorname{mixedMemory}\left(P, n, F, M, m, xi\right)) \Leftrightarrow ((\forall N : \mathbb{N}, \forall i : \mathbb{N}, (i < N) \Rightarrow (\operatorname{Filter}.\operatorname{Eventually}\left((omega:Omega \mapsto (\operatorname{memorySpin}\left(F, M, m, xi, N, i, omega\right) = -1) \lor (\operatorname{memorySpin}\left(F, M, m, xi, N, i, omega\right) = 1)), \operatorname{ae}\left(P\right)\right))) \land (\exists V : \operatorname{Finset}\left(\mathbb{N}\right), (((V.\operatorname{card} = n) \land (\forall N : \mathbb{N}, (V \subseteq \operatorname{Finset}.\operatorname{range}\left(M\left(N\right)\right)) \land (\forall mu : \mathbb{N}, (mu \in \operatorname{Finset}.\operatorname{range}\left(M\left(N\right)\right)) \Rightarrow ((\neg m\left(mu\right) = 0) \Leftrightarrow (mu \in V))))) \land (\forall mu : \mathbb{N}, (mu \in V) \Rightarrow (\operatorname{Filter}.\operatorname{Eventually}\left((omega:Omega \mapsto \operatorname{Tendsto}\left((N:\mathbb{N} \mapsto (N:\mathbb{R})^{-1} \cdot \sum_{i \in \operatorname{Finset}.\operatorname{range}\left(N\right)} xi\left(mu, i, omega\right) \cdot \operatorname{memorySpin}\left(F, M, m, xi, N, i, omega\right)), \operatorname{atTop}, \operatorname{nhds}\left(m\left(mu\right)\right)\right)), \operatorname{ae}\left(P\right)\right)))) \land (\forall mu : \mathbb{N}, (\exists N : \mathbb{N}, mu < M\left(N\right)) \Rightarrow ((\neg mu \in V) \Rightarrow (\operatorname{Filter}.\operatorname{Eventually}\left((omega:Omega \mapsto \operatorname{Tendsto}\left((N:\mathbb{N} \mapsto (N:\mathbb{R})^{-1} \cdot \sum_{i \in \operatorname{Finset}.\operatorname{range}\left(N\right)} xi\left(mu, i, omega\right) \cdot \operatorname{memorySpin}\left(F, M, m, xi, N, i, omega\right)), \operatorname{atTop}, \operatorname{nhds}\left(0\right)\right)), \operatorname{ae}\left(P\right)\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.mixedMemory` (`✓ std3`).

*Citation.* Véronique Gayrard (2025). *Mixed memories in Hopfield networks*. URL: <https://arxiv.org/abs/2504.04879v2>.

*Commentary.*

Definition 1.1, p. 4: "Let $F$ be a smooth function whose derivative satisfies $F'(x)>0$, for all $x > 0$. Given $n \in \mathbb{N}$ independent of $N$, $n$-mixed memories of type $F$ are configurations in $\mathcal{S}_{N}$ denoted by $\xi^{(N)}(m) = (\xi_{i}(m))_{1 \leq i \leq N}$ and defined as" the displayed spin formula. "(i) $m$ has exactly $n$ non-zero components, i.e. there exists a subset $V$⊂{1,…,M} of cardinality $|V| = n$ such that $m_{\mu} \ne 0$ if and only if $\mu \in V$." "Let {μ₁,…,μₙ} be an enumeration of the elements of $V$ and, for each $1 \leq \nu \leq n$, set $m_{\mu_{\nu}} = \widehat{m}_{\nu}$. Then, for each $1 \leq \nu \leq n$, the normalised overlap of $\xi^{(N)}(m)$ with the pattern $\xi^{\mu_{\nu}}$ converges to $\widehat{m}_{\nu}$ as $N$ diverges," and "and it converges to zero else," with probability one in (1.2.1.2) and (1.2.1.3). The formula records that configurations are binary almost surely. Each occupied coordinate converges to its coefficient; every coordinate appearing at some size and outside V converges to zero. The support V is independent of N. The hypotheses on F, n, M and the coordinate bounds are bound in claim.

**Definition 1.8 (Gayrard's Conjecture 1.4).**

$$(claim) \Leftrightarrow (\forall Omega : \operatorname{Type}, [\operatorname{MeasurableSpace}\left(Omega\right)] \forall P : \operatorname{Measure}\left(Omega\right), [\operatorname{IsProbabilityMeasure}\left(P\right)] \forall xi : (\mathbb{N}) \to ((\mathbb{N}) \to ((Omega) \to (\mathbb{R}))), (\forall mu : \mathbb{N}, \forall i : \mathbb{N}, \operatorname{Measurable}\left(xi\left(mu, i\right)\right)) \Rightarrow ((\operatorname{iIndepFun}\left((pair:\mathbb{N} \times \mathbb{N} \mapsto xi\left(pair.\operatorname{fst}, pair.\operatorname{snd}\right)), P\right)) \Rightarrow ((\forall mu : \mathbb{N}, \forall i : \mathbb{N}, (P\left(\{omega:Omega \mid xi\left(mu, i, omega\right) = 1\}\right) = \frac{1}{2}) \land (P\left(\{omega:Omega \mid xi\left(mu, i, omega\right) = -1\}\right) = \frac{1}{2})) \Rightarrow (\forall F : (\mathbb{R}) \to (\mathbb{R}), (\operatorname{ContDiff}\left(\mathbb{R}, \operatorname{Top}.\operatorname{top}, F\right)) \Rightarrow ((\forall x : \mathbb{R}, (0 < x) \Rightarrow (0 < \operatorname{deriv}\left(F, x\right))) \Rightarrow (\forall n : \mathbb{N}, (\operatorname{Odd}\left(n\right)) \Rightarrow (\forall M : (\mathbb{N}) \to (\mathbb{N}), (\operatorname{Monotone}\left(M\right)) \Rightarrow (\forall m : (\mathbb{N}) \to (\mathbb{R}), (\forall mu : \mathbb{N}, (-1 \le m\left(mu\right)) \land (m\left(mu\right) \le 1)) \Rightarrow ((\operatorname{mixedMemory}\left(P, n, F, M, m, xi\right)) \Leftrightarrow (\forall N : \mathbb{N}, (mu:\operatorname{Fin}\left(M\left(N\right)\right) \mapsto m\left(\operatorname{val}\left(mu\right)\right)) \in \operatorname{coefficientSet}\left(n, F, M\left(N\right)\right)))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.claim` (`✓ std3`).

*Citation.* Véronique Gayrard (2025). *Mixed memories in Hopfield networks*. URL: <https://arxiv.org/abs/2504.04879v2>.

*Commentary.*

Conjecture 1.4, printed p. 6: "Given any $n \in \mathbb{N}$ odd, $\xi^{(N)}(m)$ is an $n$-mixed memory of type $F$ if and only if $m \in \mathcal{M}_{n,F}$." The standing sentence on p. 4 is: "Throughout the paper, $n \in \mathbb{N}$ is chosen to be independent of $N$ and $M$ is chosen to be a non-decreasing function of $N$." An infinite deterministic sequence m represents coherent restrictions to the first M(N) coordinates. Membership is checked on each restriction. The probability space and jointly independent measurable family xi are arbitrary; both signs have mass 1/2. F is smooth with positive derivative on the positive half-line, n is odd, M is monotone, and every coefficient lies in [-1,1]. The two bracketed Lean instance arguments are anonymous.

**Theorem 1.9 (An asymmetric five-pattern counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/gayrard-2025-mixed-memory-converse-refutation` (refuted) by `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gayrard-2025-mixed-memory-converse-refutation","declaration_gid":"D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Véronique Gayrard (2025). *Mixed memories in Hopfield networks*. URL: <https://arxiv.org/abs/2504.04879v2>.

*Commentary.*

For F(x)=x²/2 and M(N)=5, take m=(5/8,3/8,3/8,1/8,1/8), padded by zeros. The integer fields 5x₁+3x₂+3x₃+x₄+x₅ never vanish. Summing each coordinate times their sign over all 32 cube points gives (20,12,12,4,4). An infinite product of fair Boolean coordinates supplies the independent patterns; the strong law yields the five normalized overlap limits. There are no unused coordinates among the first five. The allowable compositions of five are (5), (2,3), (4,1), (2,2,1), and every padded block coordinate has absolute value at most 1/2. Permutations and the prescribed sign powers preserve this bound, while m₁=5/8. Theorem 1.2's sufficient direction is compatible with this failure of necessity. No local-minimum assertion is made.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.allowable`
- Truth anchor: `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.blockVector`
- Truth anchor: `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.coefficientSet`
- Truth anchor: `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.gamma`
- Truth anchor: `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.hierarchySystem`
- Truth anchor: `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.memorySpin`
- Truth anchor: `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.mixedMemory`
- Truth anchor: `D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.result`
- Dependency: [D5/S3/Combinatorics/IsingUniquenessSets](../../Combinatorics/IsingUniquenessSets.md)
- Dependency: [D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound](../../Quantum/Entanglement/PrecessionSpinOneSeparableBound.md)
