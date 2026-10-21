# A twelve-element atomistic lattice answers Question 7.4

## Abstract

A finite lattice separates weak and strong coset-likeness.

**Definition 1.1 (The join-irreducible set).**

$$\forall L \in \operatorname{Type},\; [\operatorname{Lattice}\left(L\right)] [\operatorname{BoundedOrder}\left(L\right)] [\operatorname{Fintype}\left(L\right)],\ \operatorname{J}\left(L\right) = \operatorname{Finset}.\operatorname{filter}\left(SupIrred, (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(L\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.J` (`✓ std3`).

*Citation.* Besfort Shala (2024). *The Probabilistic Zeta Function of a Finite Lattice*. URL: <https://arxiv.org/abs/2112.13766v6>.

*Commentary.*

For a finite bounded lattice L, J is the finite set of elements satisfying Mathlib's SupIrred predicate.

**Definition 1.2 (Join-irreducibles below an element).**

$$\forall L \in \operatorname{Type},\; [\operatorname{Lattice}\left(L\right)] [\operatorname{BoundedOrder}\left(L\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableLE}\left(L\right)],\ \forall x \in L,\; \operatorname{Jx}\left(x\right) = \operatorname{Finset}.\operatorname{filter}\left(\lambda (j: L) \mapsto (j \le x), \operatorname{J}\left(L\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.Jx` (`✓ std3`).

*Citation.* Besfort Shala (2024). *The Probabilistic Zeta Function of a Finite Lattice*. URL: <https://arxiv.org/abs/2112.13766v6>.

*Commentary.*

Jx x filters J by the order relation j ≤ x.

**Definition 1.3 (The atom-index ratio).**

$$\forall L \in \operatorname{Type},\; [\operatorname{Lattice}\left(L\right)] [\operatorname{BoundedOrder}\left(L\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableLE}\left(L\right)],\ \forall x \in L,\; \operatorname{index}\left(x\right) = \frac{(\operatorname{Finset}.\operatorname{card}\left(\operatorname{J}\left(L\right)\right): \mathbb{Q})}{(\operatorname{Finset}.\operatorname{card}\left(\operatorname{Jx}\left(x\right)\right): \mathbb{Q})}$$

*Formalization.* `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.index` (`✓ std3`).

*Citation.* Besfort Shala (2024). *The Probabilistic Zeta Function of a Finite Lattice*. URL: <https://arxiv.org/abs/2112.13766v6>.

*Commentary.*

index x is the rational ratio of the cardinality of J to the cardinality of Jx x.

**Definition 1.4 (The probabilistic zeta function).**

$$\forall L \in \operatorname{Type},\; [\operatorname{Lattice}\left(L\right)] [\operatorname{BoundedOrder}\left(L\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] [\operatorname{DecidableLE}\left(L\right)] [\operatorname{LocallyFiniteOrder}\left(L\right)],\ \forall s \in \mathbb{C},\; \operatorname{P}\left(s\right) = \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{erase}\left((\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(L\right)), (\operatorname{Bot}.\operatorname{bot}: L)\right), \lambda (x: L) \mapsto ((\operatorname{IncidenceAlgebra}.\operatorname{mu}\left(\mathbb{Z}, x, (\operatorname{Top}.\operatorname{top}: L)\right): \mathbb{C}) \cdot (((\operatorname{index}\left(x\right): \mathbb{Q}): \mathbb{C}))^{- (s)})\right)$$

*Formalization.* `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.P` (`✓ std3`).

*Citation.* Besfort Shala (2024). *The Probabilistic Zeta Function of a Finite Lattice*. URL: <https://arxiv.org/abs/2112.13766v6>.

*Commentary.*

P L s sums the upper-interval Möbius coefficients over all elements except bottom, weighted by the complex power of the rational index.

**Definition 1.5 (Strong coset-likeness).**

$$\forall L \in \operatorname{Type},\; [\operatorname{Lattice}\left(L\right)] [\operatorname{BoundedOrder}\left(L\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableLE}\left(L\right)],\ \operatorname{StronglyCosetLike}\left(L\right) = (\forall x \in L,\; x \ne (\operatorname{Bot}.\operatorname{bot}: L) \Rightarrow (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Jx}\left(x\right)\right) \mid \operatorname{Finset}.\operatorname{card}\left(\operatorname{J}\left(L\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.StronglyCosetLike` (`✓ std3`).

*Citation.* Besfort Shala (2024). *The Probabilistic Zeta Function of a Finite Lattice*. URL: <https://arxiv.org/abs/2112.13766v6>.

*Commentary.*

Strong coset-likeness requires the cardinality of Jx x to divide the cardinality of J for every non-bottom element.

**Definition 1.6 (Weak coset-likeness).**

$$\forall L \in \operatorname{Type},\; [\operatorname{Lattice}\left(L\right)] [\operatorname{BoundedOrder}\left(L\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] [\operatorname{DecidableLE}\left(L\right)] [\operatorname{LocallyFiniteOrder}\left(L\right)],\ \operatorname{WeaklyCosetLike}\left(L\right) = (\exists N \in \mathbb{N},\; \exists a \in \mathbb{N} \to \mathbb{Z},\; \forall s \in \mathbb{C},\; \operatorname{P}\left(s\right) = \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{Icc}\left(1, N\right), \lambda (n: \mathbb{N}) \mapsto ((\operatorname{a}\left(n\right): \mathbb{C}) \cdot ((n: \mathbb{C}))^{- (s)})\right))$$

*Formalization.* `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.WeaklyCosetLike` (`✓ std3`).

*Citation.* Besfort Shala (2024). *The Probabilistic Zeta Function of a Finite Lattice*. URL: <https://arxiv.org/abs/2112.13766v6>.

*Commentary.*

Weak coset-likeness requires P L s to have a finite ordinary Dirichlet-series representation with integer coefficients.

**Definition 1.7 (The universal form of Question 7.4).**

$$\forall L \in \operatorname{Type},\; [\operatorname{Lattice}\left(L\right)] [\operatorname{BoundedOrder}\left(L\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] [\operatorname{DecidableLE}\left(L\right)] [\operatorname{LocallyFiniteOrder}\left(L\right)] \operatorname{IsAtomistic}\left(L\right) \Rightarrow (\operatorname{WeaklyCosetLike}\left(L\right) \Rightarrow (\operatorname{StronglyCosetLike}\left(L\right)))$$

*Formalization.* `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.claim` (`✓ std3`).

*Citation.* Besfort Shala (2024). *The Probabilistic Zeta Function of a Finite Lattice*. URL: <https://arxiv.org/abs/2112.13766v6>.

*Commentary.*

Question 7.4 asks verbatim: ‘Does there exist a weakly coset-like atomistic lattice that is not strongly coset-like?’ The formal claim is its universal negation: every finite atomistic weakly coset-like lattice is strongly coset-like.

**Theorem 1.8 (The universal implication is false).**

$$\neg \left(\forall L \in \operatorname{Type},\; [\operatorname{Lattice}\left(L\right)] [\operatorname{BoundedOrder}\left(L\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] [\operatorname{DecidableLE}\left(L\right)] [\operatorname{LocallyFiniteOrder}\left(L\right)] \operatorname{IsAtomistic}\left(L\right) \Rightarrow (\operatorname{WeaklyCosetLike}\left(L\right) \Rightarrow (\operatorname{StronglyCosetLike}\left(L\right)))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Besfort Shala (2024). *The Probabilistic Zeta Function of a Finite Lattice*. URL: <https://arxiv.org/abs/2112.13766v6>.

*Commentary.*

The twelve-element lattice has eight singleton join-irreducibles. Its element x has three join-irreducibles below it, so 3 does not divide 8. The upper Möbius coefficient of x vanishes, and the remaining terms give P L s = 1 − 2^(−s) − 4·8^(−s), an ordinary Dirichlet series. Thus the lattice is weakly coset-like but not strongly coset-like, refuting the universal implication and answering the question affirmatively. The d-divisible partition-lattice question and minimality are not settled here.

## References

- Truth anchor: `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.J`
- Truth anchor: `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.Jx`
- Truth anchor: `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.P`
- Truth anchor: `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.StronglyCosetLike`
- Truth anchor: `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.WeaklyCosetLike`
- Truth anchor: `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.claim`
- Truth anchor: `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.index`
- Truth anchor: `D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.result`
