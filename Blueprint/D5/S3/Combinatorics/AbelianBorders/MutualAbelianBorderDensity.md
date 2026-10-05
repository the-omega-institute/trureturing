# Mutual Abelian-Border Densities of Binary Word Pairs

## Abstract

Both binary mutual abelian-border densities have limits, with witnesses 1 and 0.

**Definition 1.1 (Binary words).**

$$\forall n \in \mathbb{N},\; \operatorname{Word}\left(n\right) = \left(\operatorname{Fin}\left(n\right) \to Bool\right)$$

*Formalization.* `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A binary word of length n is a function from Fin(n) to Bool. Positions are numbered from 0 to n-1, with false and true encoding the paper's letters a and b. The ordered pair carrier is Word(n) × Word(n).

**Theorem 1.2 (Reflection count for nonnegative walks).**

$$\forall walks \in (n: \mathbb{N}) \to \left(\mathbb{N} \to \operatorname{Set}\left(\operatorname{Fin}\left(n + 1\right) \to \mathbb{N}\right)\right),\; (\forall n \in \mathbb{N},\; \forall x \in \mathbb{N},\; \operatorname{walks}\left(n, x\right) = \{s \in \operatorname{Fin}\left(n + 1\right) \to \mathbb{N} \mid (s\left(0\right) = x) \land (\forall i \in \operatorname{Fin}\left(n\right),\; s\left(i + 1\right) = s\left(i\right) + 1 \lor s\left(i + 1\right) + 1 = s\left(i\right))\}) \Rightarrow (\forall n \in \mathbb{N},\; \forall x \in \mathbb{N},\; (\operatorname{Finite}\left(\operatorname{walks}\left(n, x\right)\right)) \land (\operatorname{ncard}\left(\operatorname{walks}\left(n, x\right)\right) = \operatorname{sum}\left(\operatorname{range}\left(n + 1\right), \lambda d \mapsto \operatorname{ifThenElse}\left((n < 2 \cdot d + x + 2) \land (2 \cdot d \le n + x), \operatorname{choose}\left(n, d\right), 0\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/RandomWalks/WalkCount.walk_count` (`✓ std3`). ∎

*Citation.* Marilena Jianu and Leonard Dăuş (2025). *The number of Dyck-type lattice paths and related sequences*. URL: <https://dmi.utcb.ro/wp-content/uploads/2025/09/proceeeings2025.pdf>.

*Commentary.*

For any family walks with the displayed defining equation, every set walks(n,x) is finite and its cardinality is the reflection sum. The parameter n is the number of steps, and x is the initial height; both range over all natural numbers. The two evaluations at i+1 and i use i.succ and i.castSucc. A first-step decomposition gives two disjoint families, with the downward family present only for x at least 1. Pascal's rule gives the same recursion for the sum, and induction identifies their counts. The family used here is SurvivingWalkRecurrence.walks. No second walk definition is needed.

**Definition 1.3 (Internal abelian borders).**

$$\forall n \in \mathbb{N},\; \forall p \in \operatorname{Word}\left(n\right) \times \operatorname{Word}\left(n\right),\; \operatorname{internal}\left(p\right) \Leftrightarrow (\exists r \in \mathbb{N},\; (r \in \operatorname{Icc}\left(1, \operatorname{NatSub}\left(n, 1\right)\right)) \land (\forall b \in Bool,\; \operatorname{count}\left(\operatorname{drop}\left(\operatorname{ofFn}\left(\operatorname{fst}\left(p\right)\right), \operatorname{NatSub}\left(n, r\right)\right), b\right) = \operatorname{count}\left(\operatorname{take}\left(\operatorname{ofFn}\left(\operatorname{snd}\left(p\right)\right), r\right), b\right)))$$

*Formalization.* `D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity.internal` (`✓ std3`).

*Citation.* Anuran Maity, K. V. Krishna (2025). *Mutually Abelian-Bordered Binary Words*. DOI: [10.1007/978-3-032-17801-5_6](https://doi.org/10.1007/978-3-032-17801-5_6). URL: <https://arxiv.org/abs/2509.20773v1>.

*Commentary.*

“We say a pair of words $(x, y)$ is an internal abelian-border of $(u, v)$ if $x$ is a nonempty proper suffix of $u$ and  $y$ is a proper prefix of $v$ such that $x \sim_{\mathrm{abl}} y$.” (Section 1, Definition 1.1, p. 2.)

The two words have the same length n. Abelian equivalence is equality of the counts of both Boolean letters. Icc(1,NatSub(n,1)) is the finite closed natural interval; NatSub is truncated natural subtraction. The suffix is drop(ofFn(fst(p)),NatSub(n,r)), and the prefix is take(ofFn(snd(p)),r). Equal counts force equal lengths, so both factors are nonempty and proper.

**Definition 1.4 (External abelian borders).**

$$\forall n \in \mathbb{N},\; \forall p \in \operatorname{Word}\left(n\right) \times \operatorname{Word}\left(n\right),\; \operatorname{external}\left(p\right) \Leftrightarrow (\exists r \in \mathbb{N},\; (r \in \operatorname{Icc}\left(1, \operatorname{NatSub}\left(n, 1\right)\right)) \land (\forall b \in Bool,\; \operatorname{count}\left(\operatorname{take}\left(\operatorname{ofFn}\left(\operatorname{fst}\left(p\right)\right), r\right), b\right) = \operatorname{count}\left(\operatorname{drop}\left(\operatorname{ofFn}\left(\operatorname{snd}\left(p\right)\right), \operatorname{NatSub}\left(n, r\right)\right), b\right)))$$

*Formalization.* `D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity.external` (`✓ std3`).

*Citation.* Anuran Maity, K. V. Krishna (2025). *Mutually Abelian-Bordered Binary Words*. DOI: [10.1007/978-3-032-17801-5_6](https://doi.org/10.1007/978-3-032-17801-5_6). URL: <https://arxiv.org/abs/2509.20773v1>.

*Commentary.*

“Similarly, we say the  pair $(x, y)$ is an external abelian-border of $(u, v)$ if $x$ is a nonempty proper prefix of $u$ and  $y$ is a proper suffix of $v$ such that $x \sim_{\mathrm{abl}} y$.” (Section 1, Definition 1.1, p. 2.)

The prefix of the first word is compared with the suffix of the second word, for the same nonempty proper length r.

**Definition 1.5 (Counting mutually abelian-bordered pairs).**

$$\forall n \in \mathbb{N},\; \operatorname{M}\left(n\right) = \operatorname{card}\left(\operatorname{filter}\left(\lambda(p: \operatorname{Word}\left(n\right) \times \operatorname{Word}\left(n\right)) \mapsto ((\operatorname{internal}\left(p\right)) \land (\operatorname{external}\left(p\right))), \operatorname{univ}\left(\operatorname{Word}\left(n\right) \times \operatorname{Word}\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity.M` (`✓ std3`).

*Citation.* Anuran Maity, K. V. Krishna (2025). *Mutually Abelian-Bordered Binary Words*. DOI: [10.1007/978-3-032-17801-5_6](https://doi.org/10.1007/978-3-032-17801-5_6). URL: <https://arxiv.org/abs/2509.20773v1>.

*Commentary.*

“A pair of words $(u, v)$ is said to be mutually abelian-bordered if $(u, v)$ has both internal abelian-border and external abelian-border.” (Section 1, Definition 1.1, p. 2.)

“The number of MAB pairs $(u, v)$ with $\left|u\right| = \left|v\right| = n$ is denoted by $\mathcal{M}(n)$.” (Section 2, p. 3.)

univ(A) denotes the finite set of all inhabitants of the finite type A; filter(P,s) retains the elements of s satisfying P, and card denotes Finset.card. The finite set contains ordered pairs with both kinds of border. Internal and external border lengths may differ; overlapping borders are allowed.

**Definition 1.6 (Counting mutually abelian-unbordered pairs).**

$$\forall n \in \mathbb{N},\; \operatorname{Mbar}\left(n\right) = \operatorname{card}\left(\operatorname{filter}\left(\lambda(p: \operatorname{Word}\left(n\right) \times \operatorname{Word}\left(n\right)) \mapsto ((\neg \operatorname{internal}\left(p\right)) \land (\neg \operatorname{external}\left(p\right))), \operatorname{univ}\left(\operatorname{Word}\left(n\right) \times \operatorname{Word}\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity.Mbar` (`✓ std3`).

*Citation.* Anuran Maity, K. V. Krishna (2025). *Mutually Abelian-Bordered Binary Words*. DOI: [10.1007/978-3-032-17801-5_6](https://doi.org/10.1007/978-3-032-17801-5_6). URL: <https://arxiv.org/abs/2509.20773v1>.

*Commentary.*

“If a pair of words $(u, v)$ has neither an internal abelian-border nor an external abelian-border, then $(u, v)$ is said to be mutually abelian-unbordered pair of words.” (Section 1, Definition 1.2, p. 2.)

“Let $\overline{\mathcal{M}}(n)$  denote the number of mutually abelian-unbordered pairs of binary words $(u, v)$ where $\left|u\right| = \left|v\right| = n$.” (Section 3, p. 25.)

These pairs have neither kind of border. In particular M(1)=0 and Mbar(1)=4.

**Definition 1.7 (The published limit question).**

$$claim \Leftrightarrow ((\exists L \in \mathbb{R},\; \operatorname{Tendsto}\left(\left(\frac{\operatorname{ofRealNat}\left(\operatorname{M}\left(n\right)\right)}{4^{n}}\right)_{n \in \mathbb{N}}, atTop, \operatorname{nhds}\left(L\right)\right)) \land (\exists L \in \mathbb{R},\; \operatorname{Tendsto}\left(\left(\frac{\operatorname{ofRealNat}\left(\operatorname{Mbar}\left(n\right)\right)}{4^{n}}\right)_{n \in \mathbb{N}}, atTop, \operatorname{nhds}\left(L\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity.claim` (`✓ std3`).

*Citation.* Anuran Maity, K. V. Krishna (2025). *Mutually Abelian-Bordered Binary Words*. DOI: [10.1007/978-3-032-17801-5_6](https://doi.org/10.1007/978-3-032-17801-5_6). URL: <https://arxiv.org/abs/2509.20773v1>.

*Commentary.*

“Do the limits $\lim_{n\to\infty} \frac{\mathcal{M}(n)}{2^{2n}}$ and $\lim_{n\to\infty} \frac{\overline{\mathcal{M}}(n)}{2^{2n}}$ exist?” (Section 5, Conclusion, question 1, p. 29.)

The two existential real limits are independent. The denominator 4^n equals 2^(2n). ofRealNat is the natural-to-real coercion, so every displayed quotient is real division. The definitions also assign counts at n=0; this finite initial extension does not affect either limit.

**Theorem 1.8 (Both limits exist).**

$$(\exists L \in \mathbb{R},\; \operatorname{Tendsto}\left(\left(\frac{\operatorname{ofRealNat}\left(\operatorname{M}\left(n\right)\right)}{4^{n}}\right)_{n \in \mathbb{N}}, atTop, \operatorname{nhds}\left(L\right)\right)) \land (\exists L \in \mathbb{R},\; \operatorname{Tendsto}\left(\left(\frac{\operatorname{ofRealNat}\left(\operatorname{Mbar}\left(n\right)\right)}{4^{n}}\right)_{n \in \mathbb{N}}, atTop, \operatorname{nhds}\left(L\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anuran Maity, K. V. Krishna (2025). *Mutually Abelian-Bordered Binary Words*. DOI: [10.1007/978-3-032-17801-5_6](https://doi.org/10.1007/978-3-032-17801-5_6). URL: <https://arxiv.org/abs/2509.20773v1>.

*Commentary.*

“Do the limits $\lim_{n\to\infty} \frac{\mathcal{M}(n)}{2^{2n}}$ and $\lim_{n\to\infty} \frac{\overline{\mathcal{M}}(n)}{2^{2n}}$ exist?” (Section 5, Conclusion, question 1, p. 29.)

The proof chooses the first limit to be 1 and the second to be 0. Reverse the first word and interleave it with the complemented second word. An internal abelian border becomes a zero at an even time of the resulting unit-step walk. Odd times cannot be zero. Border-free prefixes embed in nonnegative walks after fixing their first sign. The reflection count bounds the exceptional pairs by a central binomial coefficient. Its normalized value tends to zero; swapping the two words gives the same bound for external borders. The union bound and squeeze give both limits.

## References

- Truth anchor: `D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity.M`
- Truth anchor: `D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity.Mbar`
- Truth anchor: `D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity.claim`
- Truth anchor: `D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity.external`
- Truth anchor: `D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity.internal`
- Truth anchor: `D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity.result`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.Word`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/WalkCount.walk_count`
- Dependency: [D5/S3/Arith/AbsoluteValues/Heights/Gelfond](../../Arith/AbsoluteValues/Heights/Gelfond.md)
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs](../NarayanaStrip/CiglerStripExpansionDefs.md)
- Dependency: [D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace](../../ConceptDynamics/ExperimentBoundary/BoundedRunSpace.md)
- Dependency: [D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence](../../StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.md)
