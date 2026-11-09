# Finite tournament path defects and convergence

## Abstract

Finite tournament path defects and convergence

An orientation is a list of signs, with true denoting a forward arc and false a backward arc. Its flips count adjacent unequal signs. ArcPreserving quantifies over every map from Fin(length+1) to Fin(N); maps need not be injective. The density homDensity is homCount divided by N^(length+1). TAS quantifies over every positive N and every loopless tournament relation on Fin(N), with bound (1/2)^length. Enumeration of the vertices identifies these hosts with arbitrary finite nonempty loopless tournaments. The function f is the maximum of precisely those m in {0,...,k} for which every length-k orientation with fewer than m flips is TAS. The set contains zero. No property at length zero is used. The motivating question is Question 6.1 in Hao Chen and Yupeng Lin, Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko, https://arxiv.org/abs/2609.14655v1.

**Definition 1.1 (Loopless tournaments).**

$$\forall V \in Type,\; \forall R \in V \to \left(V \to Prop\right),\; \operatorname{IsTournament}\left(R\right) \Leftrightarrow \left(\left(\forall i \in V,\; \neg \operatorname{R}\left(i, i\right)\right) \land \left(\forall i \in V,\; \forall j \in V,\; i \ne j \Rightarrow \left(\left(\operatorname{R}\left(i, j\right) \land \neg \operatorname{R}\left(j, i\right)\right) \lor \left(\operatorname{R}\left(j, i\right) \land \neg \operatorname{R}\left(i, j\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.IsTournament` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

This is the existing repository tournament predicate: no loops and exactly one directed arc on every distinct pair.

**Definition 1.2 (Adjacent unequal signs).**

$$\operatorname{flips}\left(\operatorname{nil}\left(\right)\right) = 0 \land \left(\left(\forall a \in Bool,\; \operatorname{flips}\left(\operatorname{singleton}\left(a\right)\right) = 0\right) \land \left(\forall a \in Bool,\; \forall b \in Bool,\; \forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{flips}\left(\operatorname{cons}\left(a, \operatorname{cons}\left(b, w\right)\right)\right) = \operatorname{if}\left(a = b, 0, 1\right) + \operatorname{flips}\left(\operatorname{cons}\left(b, w\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.flips` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

The empty word and a singleton have no flips. Every unequal adjacent pair adds one. This agrees with counting internal sources and sinks.

**Definition 1.3 (All arc-preserving vertex assignments).**

$$\forall V \in Type,\; \forall R \in V \to \left(V \to Prop\right),\; \forall w \in \operatorname{List}\left(Bool\right),\; \forall p \in \operatorname{Fin}\left(\operatorname{length}\left(w\right) + 1\right) \to V,\; \operatorname{ArcPreserving}\left(R, w, p\right) \Leftrightarrow \left(\forall i \in \operatorname{Fin}\left(\operatorname{length}\left(w\right)\right),\; \operatorname{if}\left(\operatorname{get}\left(w, i\right), \operatorname{R}\left(\operatorname{apply}\left(p, \operatorname{castSucc}\left(i\right)\right), \operatorname{apply}\left(p, \operatorname{succ}\left(i\right)\right)\right), \operatorname{R}\left(\operatorname{apply}\left(p, \operatorname{succ}\left(i\right)\right), \operatorname{apply}\left(p, \operatorname{castSucc}\left(i\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.ArcPreserving` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

ArcCondition uses the forward arc from p(castSucc i) to p(succ i) for true, and the reverse arc for false. Assignments are unrestricted functions; distinct source vertices may have the same image.

**Definition 1.4 (The exact number of all path homomorphisms).**

$$\forall V \in Type,\; \forall R \in V \to \left(V \to Prop\right),\; \forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{homCount}\left(R, w\right) = \operatorname{Natcard}\left(\operatorname{Hom}\left(R, w\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.homCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Hom(R,w) is the subtype of all functions Fin(length(w)+1) → V satisfying ArcPreserving. Nat.card is the natural cardinality of this subtype.

**Definition 1.5 (Homomorphism density).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall R \in V \to \left(V \to Prop\right),\; \forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{homDensity}\left(R, w\right) = \frac{\operatorname{homCount}\left(R, w\right)}{\operatorname{card}\left(V\right)^{\operatorname{length}\left(w\right) + 1}}$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.homDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

The numerator and host order are coerced to real numbers before division.

**Definition 1.6 (Tournament anti-Sidorenko words).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{TAS}\left(w\right) \Leftrightarrow \left(\forall N \in \mathbb{N},\; 0 < N \Rightarrow \left(\forall R \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to Prop\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow \operatorname{homDensity}\left(R, w\right) \le \frac{1}{2}^{\operatorname{length}\left(w\right)}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.TAS` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

The bound holds for every positive host order and every tournament relation on that carrier. The arbitrary-host theorem proves that enumeration imposes no restriction.

**Definition 1.7 (Admissible strict thresholds).**

$$\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; m \in \operatorname{thresholds}\left(k\right) \Leftrightarrow \left(m \le k \land \left(\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{length}\left(w\right) = k \Rightarrow \left(\operatorname{flips}\left(w\right) < m \Rightarrow \operatorname{TAS}\left(w\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.thresholds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

The threshold ranges from zero through k. The comparison on flips is strict.

**Definition 1.8 (The exact saturated maximum).**

$$\forall k \in \mathbb{N},\; \operatorname{f}\left(k\right) = \operatorname{max}\left(\operatorname{thresholds}\left(k\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.f` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Zero is an admissible threshold, so this finite maximum exists. The maximum may equal k, and this saturated case is included in the convergence proof.

**Definition 1.9 (Repeated concatenation).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall m \in \mathbb{N},\; \operatorname{repeatWord}\left(w, m\right) = \operatorname{flatten}\left(\operatorname{replicate}\left(m, w\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.repeatWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Flatten m copies of w, giving the empty word when m=0. Its length is m length(w). The proved bounds give at most m(flips(w)+1) flips and transfer equal to transfer(A,w)^m.

**Definition 1.10 (Forward and reverse transfer factors).**

$$\forall V \in Type,\; \forall A \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \forall b \in Bool,\; \operatorname{step}\left(A, b\right) = \operatorname{if}\left(b = true, A, \operatorname{transpose}\left(A\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.step` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

A true sign uses A; a false sign uses its transpose.

**Definition 1.11 (The ordered transfer product).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall A \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{transfer}\left(A, w\right) = \operatorname{prod}\left(\operatorname{map}\left(\operatorname{step}\left(A\right), w\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Take the matrix product in list order. The empty word has identity transfer.

**Definition 1.12 (Average transfer mass).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall M \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \operatorname{mass}\left(M\right) = \frac{\operatorname{entrysum}\left(M\right)}{\operatorname{card}\left(V\right)}$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.mass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Entrysum(M) is the sum over all ordered pairs of indices. Divide by the number of indices, not its square.

**Definition 1.13 (Reverse order and complement every sign).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{reflect}\left(w\right) = \operatorname{map}\left(Boolnot, \operatorname{reverse}\left(w\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.reflect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

The reflected word has the same length and the same number of flips, as proved by the reversal and complement identities.

**Definition 1.14 (The normalized tournament arc matrix).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall R \in V \to \left(V \to Prop\right),\; \forall i \in V,\; \forall j \in V,\; \operatorname{entry}\left(\operatorname{normalizedArcMatrix}\left(R\right), i, j\right) = \operatorname{if}\left(\operatorname{R}\left(i, j\right), \frac{2}{\operatorname{card}\left(V\right)}, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.normalizedArcMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

A present arc has weight 2/card(V); an absent arc has weight zero.

**Definition 1.15 (Normalized matrix moments).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall C \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \forall x \in V \to \mathbb{R},\; \forall n \in \mathbb{N},\; \operatorname{moment}\left(C, x, n\right) = \frac{\operatorname{dot}\left(x, \operatorname{mulVec}\left(C^{n}, x\right)\right)}{\operatorname{dot}\left(x, x\right)}$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.moment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

The growth theorem assumes positive squared norm and positive first moment; the definition itself uses real division.

**Definition 1.16 (The spectrum of realizable defects).**

$$\forall Bad \in \mathbb{N} \to \left(\mathbb{N} \to Prop\right),\; \forall x \in \mathbb{R},\; x \in \operatorname{defectSpectrum}\left(Bad\right) \Leftrightarrow \left(x = 1 \lor \left(\exists k \in \mathbb{N},\; \exists r \in \mathbb{N},\; 0 < k \land \left(\operatorname{Bad}\left(k, r\right) \land x = \frac{r + 1}{k}\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.defectSpectrum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

A defect contributes (r+1)/k, including the cost of a join. The extra element 1 handles saturation. Every element is nonnegative.

**Definition 1.17 (The infimum of the defect spectrum).**

$$\forall Bad \in \mathbb{N} \to \left(\mathbb{N} \to Prop\right),\; \operatorname{defectLimit}\left(Bad\right) = \operatorname{sInf}\left(\operatorname{defectSpectrum}\left(Bad\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.defectLimit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

The spectrum is nonempty and bounded below by zero. Its infimum is at most one.

**Definition 1.18 (The source sign type).**

$$Sign = \left\{-1, 1\right\}$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.Sign` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Sign is the subtype of integers z with z=-1 or z=1; the displayed finite set denotes this subtype.

**Definition 1.19 (Source arcs indexed by integer signs).**

$$\forall V \in Type,\; \forall k \in \mathbb{N},\; \forall R \in V \to \left(V \to Prop\right),\; \forall x \in \operatorname{Fin}\left(k\right) \to Sign,\; \forall p \in \operatorname{Fin}\left(k + 1\right) \to V,\; \operatorname{SourceArcPreserving}\left(R, x, p\right) \Leftrightarrow \left(\forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{if}\left(\operatorname{x}\left(i\right) = 1, \operatorname{R}\left(\operatorname{apply}\left(p, \operatorname{castSucc}\left(i\right)\right), \operatorname{apply}\left(p, \operatorname{succ}\left(i\right)\right)\right), \operatorname{R}\left(\operatorname{apply}\left(p, \operatorname{succ}\left(i\right)\right), \operatorname{apply}\left(p, \operatorname{castSucc}\left(i\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.SourceArcPreserving` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

The condition is the forward arc exactly when x(i)=1, and the reverse arc otherwise. Since the only other sign is -1, this is the literal source orientation.

**Definition 1.20 (Source TAS over every finite host).**

$$\forall k \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(k\right) \to Sign,\; \operatorname{SourceTAS}\left(x\right) \Leftrightarrow \left(\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Nonempty}\left(V\right)] \forall R \in V \to \left(V \to Prop\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow \operatorname{sourceDensity}\left(R, x\right) \le \frac{1}{2}^{k}\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.SourceTAS` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Finite hosts are arbitrary types with a finite enumeration and at least one vertex. Enumeration equivalence proves equality with the Fin-labelled condition.

**Definition 1.21 (The source set of admissible thresholds).**

$$\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; m \in \operatorname{sourceThresholds}\left(k\right) \Leftrightarrow \left(m \le k \land \left(\forall x \in \operatorname{Fin}\left(k\right) \to Sign,\; \operatorname{sourceFlips}\left(x\right) < m \Rightarrow \operatorname{SourceTAS}\left(x\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.sourceThresholds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

This uses the independently defined source flip count and source TAS property. The sign and host correspondences prove that it equals thresholds(k).

**Theorem 1.22 (Every word below the maximum is TAS).**

$$\forall k \in \mathbb{N},\; \forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{length}\left(w\right) = k \Rightarrow \left(\operatorname{flips}\left(w\right) < \operatorname{f}\left(k\right) \Rightarrow \operatorname{TAS}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.tas_of_flips_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

The maximum is a member of the finite set defining thresholds, with the strict inequality on the number of flips.

**Theorem 1.23 (Every defect bounds the maximum).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \neg \operatorname{TAS}\left(w\right) \Rightarrow \operatorname{f}\left(\operatorname{length}\left(w\right)\right) \le \operatorname{flips}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.f_le_flips_of_not_tas` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

If the maximum exceeded the flip count, the preceding threshold property would make this word TAS, contradicting the defect.

**Theorem 1.24 (Concatenation multiplies transfers).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall A \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \forall u \in \operatorname{List}\left(Bool\right),\; \forall v \in \operatorname{List}\left(Bool\right),\; \operatorname{transfer}\left(A, \operatorname{append}\left(u, v\right)\right) = \operatorname{transfer}\left(A, u\right) \cdot \operatorname{transfer}\left(A, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.transfer_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

This is the ordered product law for concatenated lists.

**Theorem 1.25 (Reflected words transpose transfers).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall A \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{transfer}\left(A, \operatorname{reflect}\left(w\right)\right) = \operatorname{transpose}\left(\operatorname{transfer}\left(A, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.transfer_reflect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Reversing the factors and complementing every sign transposes the ordered product.

**Theorem 1.26 (The two extension masses have a fixed sum).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall A \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \forall M \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \forall d \in \mathbb{R},\; \left(\forall i \in V,\; \operatorname{rowsum}\left(A + \operatorname{transpose}\left(A\right), i\right) = d\right) \Rightarrow \operatorname{mass}\left(M \cdot A\right) + \operatorname{mass}\left(M \cdot \operatorname{transpose}\left(A\right)\right) = d \cdot \operatorname{mass}\left(M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.extension_mass_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Rowsum(A+A^T,i) denotes sum over j of A(i,j)+A(j,i). Expand matrix multiplication, interchange the finite sums, and use this row identity.

**Theorem 1.27 (One of two signs retains the average).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall A \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \forall M \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \forall c \in \mathbb{R},\; \operatorname{mass}\left(M \cdot A\right) + \operatorname{mass}\left(M \cdot \operatorname{transpose}\left(A\right)\right) = 2 \cdot c \cdot \operatorname{mass}\left(M\right) \Rightarrow \left(\exists b \in Bool,\; c \cdot \operatorname{mass}\left(M\right) \le \operatorname{mass}\left(M \cdot \operatorname{step}\left(A, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.exists_one_edge_padding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

If both signs gave strictly less than c times the old mass, their sum would be strictly less than twice that quantity.

**Theorem 1.28 (One-edge retention iterates to any tail length).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall A \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \forall c \in \mathbb{R},\; 0 \le c \Rightarrow \left(\left(\forall u \in \operatorname{List}\left(Bool\right),\; \exists b \in Bool,\; c \cdot \operatorname{mass}\left(\operatorname{transfer}\left(A, u\right)\right) \le \operatorname{mass}\left(\operatorname{transfer}\left(A, \operatorname{append}\left(u, \operatorname{singleton}\left(b\right)\right)\right)\right)\right) \Rightarrow \left(\forall w \in \operatorname{List}\left(Bool\right),\; \forall s \in \mathbb{N},\; \exists v \in \operatorname{List}\left(Bool\right),\; \operatorname{length}\left(v\right) = s \land c^{s} \cdot \operatorname{mass}\left(\operatorname{transfer}\left(A, w\right)\right) \le \operatorname{mass}\left(\operatorname{transfer}\left(A, \operatorname{append}\left(w, v\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.exists_padding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Choose the next sign using the stated one-edge hypothesis. Induction multiplies the lower bound by the nonnegative c at each step.

**Theorem 1.29 (Off-diagonal tournament complements).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall R \in V \to \left(V \to Prop\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow \left(\forall i \in V,\; \forall j \in V,\; \operatorname{entry}\left(\operatorname{normalizedArcMatrix}\left(R\right), i, j\right) + \operatorname{entry}\left(\operatorname{normalizedArcMatrix}\left(R\right), j, i\right) = \operatorname{if}\left(i = j, 0, \frac{2}{\operatorname{card}\left(V\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.normalizedArcMatrix_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

On the diagonal both arcs are absent. Off the diagonal exactly one direction is present and contributes 2/card(V).

**Theorem 1.30 (The tournament extension row sum).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Nonempty}\left(V\right)] \forall R \in V \to \left(V \to Prop\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow \left(\forall i \in V,\; \operatorname{rowsum}\left(\operatorname{normalizedArcMatrix}\left(R\right) + \operatorname{transpose}\left(\operatorname{normalizedArcMatrix}\left(R\right)\right), i\right) = 2 \cdot \frac{\operatorname{card}\left(V\right) - 1}{\operatorname{card}\left(V\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.normalizedArcMatrix_row_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

There are card(V)-1 off-diagonal entries, each equal to 2/card(V). The diagonal contributes zero.

**Theorem 1.31 (Log-convexity gives geometric growth).**

$$\forall a \in \mathbb{N} \to \mathbb{R},\; \operatorname{a}\left(0\right) = 1 \Rightarrow \left(0 < \operatorname{a}\left(1\right) \Rightarrow \left(\left(\forall n \in \mathbb{N},\; \operatorname{a}\left(n + 1\right)^{2} \le \operatorname{a}\left(n\right) \cdot \operatorname{a}\left(n + 2\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \operatorname{a}\left(1\right)^{n} \le \operatorname{a}\left(n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.logconvex_geometric_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Induct jointly on positivity and a(1)a(n)≤a(n+1). Log-convexity and the preceding positive term permit cancellation and give the next inequality. A second induction gives a(1)^n≤a(n), including n=0.

**Theorem 1.32 (Positive semidefinite mass dominates its first power).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{Nonempty}\left(V\right)] \forall C \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \operatorname{PosSemidef}\left(C\right) \Rightarrow \left(0 < \operatorname{mass}\left(C\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \operatorname{mass}\left(C\right)^{n} \le \operatorname{mass}\left(C^{n}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.mass_power_geometric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Specialize moment_geometric_lower to the all-ones vector. Its norm squared is the positive number card(V), and its moments are exactly the matrix-power masses.

**Theorem 1.33 (The defect-spectrum criterion).**

$$\forall F \in \mathbb{N} \to \mathbb{N},\; \forall Bad \in \mathbb{N} \to \left(\mathbb{N} \to Prop\right),\; \left(\forall k \in \mathbb{N},\; \operatorname{F}\left(k\right) \le k\right) \Rightarrow \left(\left(\forall k \in \mathbb{N},\; 0 < k \Rightarrow \left(\operatorname{F}\left(k\right) < k \Rightarrow \operatorname{Bad}\left(k, \operatorname{F}\left(k\right)\right)\right)\right) \Rightarrow \left(\left(\forall k \in \mathbb{N},\; \forall r \in \mathbb{N},\; 0 < k \Rightarrow \left(\operatorname{Bad}\left(k, r\right) \Rightarrow \left(\forall d \in \mathbb{R},\; 0 < d \Rightarrow \left(\exists K \in \mathbb{N},\; \forall n \in \mathbb{N},\; K \le n \Rightarrow \left(0 < n \Rightarrow \frac{\operatorname{F}\left(n\right)}{n} < \frac{r + 1}{k} + d\right)\right)\right)\right)\right) \Rightarrow \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists K \in \mathbb{N},\; 1 \le K \land \left(\forall n \in \mathbb{N},\; K \le n \Rightarrow \operatorname{abs}\left(\frac{\operatorname{F}\left(n\right)}{n} - \operatorname{defectLimit}\left(Bad\right)\right) < e\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.convergence_of_defect_propagation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Propagation is the displayed all-large-length bound, for every positive k, every Bad(k,r), and every positive delta: eventually F(n)/n<(r+1)/k+delta at positive n. The defect spectrum consists of 1 and every such (r+1)/k, and defectLimit is its infimum. The upper bound follows by choosing a spectrum element close to the infimum. The lower bound uses saturation or Bad(n,F(n)), yielding a loss at most 1/n. Combining the two bounds gives the exact epsilon/K conclusion.

**Theorem 1.34 (The transfer counts all homomorphisms).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{Nonempty}\left(V\right)] \forall R \in V \to \left(V \to Prop\right),\; \forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{mass}\left(\operatorname{transfer}\left(\operatorname{normalizedArcMatrix}\left(R\right), w\right)\right) = 2^{\operatorname{length}\left(w\right)} \cdot \operatorname{homDensity}\left(R, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.mass_transfer_eq_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

For a fixed initial vertex, expand the product by the next vertex and induct on the word. The finite-function cons equivalence partitions all vertex assignments by their first value. Every arc-preserving assignment contributes (2/N)^length; every other assignment contributes zero. Summing the initial vertex and dividing by N gives exactly 2^length times homDensity. Colliding assignments remain in the sum.

**Theorem 1.35 (Finite defects reach every large length).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; 0 < \operatorname{length}\left(w\right) \Rightarrow \left(\neg \operatorname{TAS}\left(w\right) \Rightarrow \left(\forall d \in \mathbb{R},\; 0 < d \Rightarrow \left(\exists K \in \mathbb{N},\; \forall n \in \mathbb{N},\; K \le n \Rightarrow \left(0 < n \Rightarrow \frac{\operatorname{f}\left(n\right)}{n} < \frac{\operatorname{flips}\left(w\right) + 1}{\operatorname{length}\left(w\right)} + d\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.defect_propagation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

A failing TAS inequality supplies an actual finite tournament and q>1. Its order exceeds one, since a one-vertex loopless host has zero transfer for every positive word. Write n=2km+s. Reflection, repetition, and a selected s-edge tail give mass at least c^(2k)(q^2)^m, which eventually exceeds one. The flip count is at most 2m(r+1)+s. Thus f(n)/n is at most (r+1)/k+2k/n. Geometric divergence and 1/n tending to zero give the displayed bound at every sufficiently large n.

**Theorem 1.36 (The exact threshold converges).**

$$FullConvergence$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.fullConvergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Apply the defect-spectrum criterion to F=f and to the actual predicate that a length-k word with r flips is not TAS. The least-defect theorem discharges the nonsaturated case; finite-defect propagation discharges the upper bound. All hypotheses are proved for the independently defined maximum f. No numerical value of the limit is asserted.

**Definition 1.37 (All placements of integer signs are represented).**

$$\forall k \in \mathbb{N},\; \operatorname{Equiv}\left(\operatorname{WordsOfLength}\left(k\right), \operatorname{Fin}\left(k\right) \to Sign\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.signVectors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

WordsOfLength(k) is the subtype of lists with length k. Sign is the subtype of integers equal to -1 or 1. The equivalence is the finite-vector/list equivalence followed pointwise by false ↔ -1 and true ↔ 1. Both inverse laws are proved. No sign placement is excluded.

**Definition 1.38 (The source counts internal sign changes).**

$$\forall k \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(k\right) \to Sign,\; \operatorname{sourceFlips}\left(x\right) = \operatorname{card}\left(\operatorname{internalflips}\left(x\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.sourceFlips` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Internalflips(x) consists of indices i<k with i+1<k and x(i)x(i+1)=-1. The definition sums its zero-or-one indicators over Fin(k). The proved sourceFlips_eq identifies this count with the recursive list flip count under signVectors, including lengths zero and one.

**Definition 1.39 (The source density on arbitrary finite hosts).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall k \in \mathbb{N},\; \forall R \in V \to \left(V \to Prop\right),\; \forall x \in \operatorname{Fin}\left(k\right) \to Sign,\; \operatorname{sourceDensity}\left(R, x\right) = \frac{\operatorname{card}\left(\operatorname{SourceHom}\left(R, x\right)\right)}{\operatorname{card}\left(V\right)^{k + 1}}$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.sourceDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

SourceHom(R,x) is the subtype of all functions Fin(k+1) → V satisfying SourceArcPreserving: sign +1 requires the forward arc and sign -1 the reverse arc at each edge. sourceDensity_eq proves equality with homDensity after sign encoding. homDensity_reindex constructs an inverse-preserving bijection of these function subtypes along any equivalence of host types and preserves the denominator.

**Theorem 1.40 (Enumeration preserves the host quantifier).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Nonempty}\left(V\right)] \forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{TAS}\left(w\right) \Rightarrow \left(\forall R \in V \to \left(V \to Prop\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow \operatorname{homDensity}\left(R, w\right) \le \frac{1}{2}^{\operatorname{length}\left(w\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.tas_arbitrary_host` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Enumerate V by Fin(card V). Pulling back the relation preserves looplessness and the unique direction on every distinct pair. The all-function bijection proves the density identity. Conversely, Fin(N) is one of the arbitrary finite hosts, so SourceTAS and TAS are equivalent under signVectors.

**Definition 1.41 (The independently defined source maximum).**

$$\forall k \in \mathbb{N},\; \operatorname{sourceF}\left(k\right) = \operatorname{max}\left(\operatorname{sourceThresholds}\left(k\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.sourceF` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

SourceThresholds(k) consists of precisely the m in {0,...,k} such that every integer sign vector x with sourceFlips(x)<m is SourceTAS. SourceTAS quantifies over all finite nonempty host types and all loopless tournament relations. Zero belongs to this finite set, so its maximum is defined. The threshold is strict, and the value k is retained when all orientations are TAS.

**Theorem 1.42 (The two exact maxima agree).**

$$\forall k \in \mathbb{N},\; \operatorname{sourceF}\left(k\right) = \operatorname{f}\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.sourceF_eq_f` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

The sign-vector equivalence preserves flips and every arc-preserving map. Host reindexing preserves every finite-host inequality. Hence the two finite sets of admissible thresholds agree, and so do their maxima at every length.

**Definition 1.43 (The source limit assertion).**

$$SourceFullConvergence \Leftrightarrow \left(\exists L \in \mathbb{R},\; \forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists K \in \mathbb{N},\; 1 \le K \land \left(\forall k \in \mathbb{N},\; K \le k \Rightarrow \operatorname{abs}\left(\frac{\operatorname{sourceF}\left(k\right)}{k} - L\right) < e\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.SourceFullConvergence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

The epsilon/K limit is taken over all positive lengths. The same independently defined source maximum occurs at every term. Its value at zero is outside the quantifiers.

**Theorem 1.44 (Answer to Question 6.1).**

$$SourceFullConvergence$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.source_fullConvergence` (`✓ std3`). ∎

*Resolves.* `Problems/chen-lin-2026-question-6-1-flip-threshold-limit` (proved) by `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.source_fullConvergence`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chen-lin-2026-question-6-1-flip-threshold-limit","declaration_gid":"D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.source_fullConvergence","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Substitute sourceF_eq_f into fullConvergence. This proves the entire existence of a limit for the source maximum, for arbitrary sign placements and every finite nonempty loopless tournament. The argument proves no prescribed limit value and uses neither a bounded host size nor a subsequence restriction.

**Definition 1.45 (Convergence over all positive lengths).**

$$FullConvergence \Leftrightarrow \left(\exists L \in \mathbb{R},\; \forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists K \in \mathbb{N},\; 1 \le K \land \left(\forall k \in \mathbb{N},\; K \le k \Rightarrow \operatorname{abs}\left(\frac{\operatorname{f}\left(k\right)}{k} - L\right) < e\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.FullConvergence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

This is the epsilon/K assertion for the source's exact strict threshold. The positive-length quantifiers retain saturation at f(k)=k.

**Theorem 1.46 (The saturated threshold is bounded).**

$$\forall k \in \mathbb{N},\; \operatorname{f}\left(k\right) \le k$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.f_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Every member of thresholds(k) belongs to {0,...,k}.

**Theorem 1.47 (A nonsaturated threshold is attained by a defect).**

$$\forall k \in \mathbb{N},\; \operatorname{f}\left(k\right) < k \Rightarrow \left(\exists w \in \operatorname{List}\left(Bool\right),\; \operatorname{length}\left(w\right) = k \land \left(\operatorname{flips}\left(w\right) = \operatorname{f}\left(k\right) \land \neg \operatorname{TAS}\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.exists_bad_at_f` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

The property holds below f(k). Its failure at f(k)+1 supplies an orientation with exactly f(k) flips, rather than merely an orientation below a different threshold.

**Theorem 1.48 (Reflection produces a Gram transfer).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall A \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{transfer}\left(A, \operatorname{append}\left(w, \operatorname{reflect}\left(w\right)\right)\right) = \operatorname{transfer}\left(A, w\right) \cdot \operatorname{transpose}\left(\operatorname{transfer}\left(A, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.reflected_pair_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Reflection reverses the word and complements every sign. It therefore transposes the product, retaining its endpoints and their correlations.

**Theorem 1.49 (Reflection amplifies the average).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Nonempty}\left(V\right)] \forall B \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \operatorname{mass}\left(B\right)^{2} \le \operatorname{mass}\left(B \cdot \operatorname{transpose}\left(B\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.reflected_mass_sq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Mass is the sum of all entries divided by the number of indices. The mass of B times its transpose is the mean of the squares of the column sums. Cauchy-Schwarz bounds it below by the square of the original mass. No independent gluing of endpoint densities is used.

**Theorem 1.50 (Every bounded remainder admits padding).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{Nonempty}\left(V\right)] \forall R \in V \to \left(V \to Prop\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow \left(\forall w \in \operatorname{List}\left(Bool\right),\; \forall s \in \mathbb{N},\; \exists v \in \operatorname{List}\left(Bool\right),\; \operatorname{length}\left(v\right) = s \land \frac{\operatorname{card}\left(V\right) - 1}{\operatorname{card}\left(V\right)}^{s} \cdot \operatorname{mass}\left(\operatorname{transfer}\left(\operatorname{normalizedArcMatrix}\left(R\right), w\right)\right) \le \operatorname{mass}\left(\operatorname{transfer}\left(\operatorname{normalizedArcMatrix}\left(R\right), \operatorname{append}\left(w, v\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.tournament_padding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Put A(i,j)=2/N when i points to j and zero otherwise. Looplessness and the unique orientation of distinct pairs give sum_j(A(i,j)+A(j,i))=2(N-1)/N. Thus the masses of the two possible one-edge extensions sum to 2(N-1)/N times the previous mass. At least one sign retains a factor (N-1)/N. Induction selects an s-edge tail retaining its s-th power, inside the same original tournament. It does not assert that an arbitrary prescribed tail is safe.

**Theorem 1.51 (All repetition counts amplify).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall C \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \operatorname{PosSemidef}\left(C\right) \Rightarrow \left(\forall x \in V \to \mathbb{R},\; 0 < \operatorname{dot}\left(x, x\right) \Rightarrow \left(0 < \operatorname{moment}\left(C, x, 1\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \operatorname{moment}\left(C, x, 1\right)^{n} \le \operatorname{moment}\left(C, x, n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.moment_geometric_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

Moment(C,x,n) is x dot C^n x divided by x dot x. Cauchy-Schwarz in the positive semidefinite form C^n gives a(n+1)^2 <= a(n)a(n+2). With a(0)=1 and a(1)>0, successive moment ratios are nondecreasing, so a(n)>=a(1)^n. This bound holds for every natural repetition count, not only a subsequence.

**Theorem 1.52 (Exponential reflected amplification).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{Nonempty}\left(V\right)] \forall B \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; 1 < \operatorname{mass}\left(B\right) \Rightarrow \left(\forall m \in \mathbb{N},\; \operatorname{mass}\left(B\right)^{2 \cdot m} \le \operatorname{mass}\left(\left(B \cdot \operatorname{transpose}\left(B\right)\right)^{m}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.reflected_power_amplification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hao Chen and Yupeng Lin (2026). *Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko*. DOI: [10.48550/arXiv.2609.14655](https://doi.org/10.48550/arXiv.2609.14655). URL: <https://arxiv.org/abs/2609.14655v1>.

*Commentary.*

The all-ones moment is the mass of the matrix power. The Gram matrix is positive semidefinite, its first mass is at least mass(B)^2, and the geometric moment bound gives mass((B B^T)^m)>=mass(B)^(2m) for every m.

For the convergence argument, call (k,r) a defect when a length-k orientation with r flips has normalized density q=2^k t(P,T)>1 in some finite host T. For a positive-length defect N>=2. The transfer B for P has mass q. The reflected word W=P reflect(P) has transfer C=B B^T, length 2k, and at most 2r+1 flips. With x the all-ones vector, moment(C,x,m)=mass(C^m). The reflection and moment bounds give mass(C^m)>=q^(2m).

For every n write n=2km+s with 0<=s<2k. The word W repeated m times has at most 2m(r+1) flips. Append the tail selected by the padding inequality. Its normalized density is at least c^s q^(2m), where c=(N-1)/N lies in (0,1). This is at least c^(2k) q^(2m), which exceeds one for all sufficiently large m. The resulting length-n path is therefore a defect for every sufficiently large n. Its flips are at most 2m(r+1)+s, hence at most ((r+1)/k)n+2k. This proves eventual upper propagation f(n)/n < (r+1)/k+delta for every positive delta.

Let L be the infimum of {1} together with all (r+1)/k from defects. This nonempty set is bounded below by zero. At a saturated length f(n)=n, one has f(n)/n>=L. At a nonsaturated length the least-defect fact gives a defect with r=f(n), so L<=(f(n)+1)/n. Thus f(n)/n>=L-1/n at every positive length. For the upper bound, choose an element of the defining set below L+epsilon/2. If it is 1, saturation bounds every f(n)/n by 1. Otherwise it is a defect ratio, and upper propagation with delta=epsilon/2 applies to every sufficiently large length. Combining this with 1/n<epsilon proves convergence to L over all positive lengths. The argument does not determine a numerical value of L.

## References

- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.ArcPreserving`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.FullConvergence`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.IsTournament`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.Sign`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.SourceArcPreserving`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.SourceFullConvergence`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.SourceTAS`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.TAS`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.convergence_of_defect_propagation`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.defectLimit`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.defectSpectrum`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.defect_propagation`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.exists_bad_at_f`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.exists_one_edge_padding`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.exists_padding`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.extension_mass_sum`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.f`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.f_le`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.f_le_flips_of_not_tas`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.flips`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.fullConvergence`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.homCount`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.homDensity`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.logconvex_geometric_lower`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.mass`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.mass_power_geometric`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.mass_transfer_eq_density`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.moment`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.moment_geometric_lower`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.normalizedArcMatrix`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.normalizedArcMatrix_complement`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.normalizedArcMatrix_row_sum`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.reflect`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.reflected_mass_sq_le`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.reflected_pair_transfer`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.reflected_power_amplification`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.repeatWord`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.signVectors`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.sourceDensity`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.sourceF`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.sourceF_eq_f`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.sourceFlips`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.sourceThresholds`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.source_fullConvergence`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.step`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.tas_arbitrary_host`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.tas_of_flips_lt`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.thresholds`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.tournament_padding`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.transfer`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.transfer_append`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.transfer_reflect`
- Dependency: [D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence](../../ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.md)
