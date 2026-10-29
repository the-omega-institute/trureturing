# Three-state overlap intervals need not be tight

## Abstract

Five overlaps of four pure states force the sixth to be one quarter, although intersection of the three-state lower bounds gives zero.

**Definition 1.1 (The three-state upper bound).**

$$\forall \left(x: \mathbb{R}\right), \left(\forall \left(y: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.upper}\left(x, y\right): \mathbb{R}\right) = \left(\operatorname{Real.sqrt}\left(\left(x\right) \cdot \left(y\right)\right) + \operatorname{Real.sqrt}\left(\left(\left(1: \mathbb{R}\right) - x\right) \cdot \left(\left(1: \mathbb{R}\right) - y\right)\right)\right)^{\left(2: \mathbb{N}\right)}\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.upper` (`✓ std3`).

*Citation.* Ernesto F. Galvão; Daniel J. Brod (2020). *Quantum and classical bounds for two-state overlaps*. DOI: [10.1103/PhysRevA.101.062110](https://doi.org/10.1103/PhysRevA.101.062110). URL: <https://arxiv.org/abs/1902.11039v3>.

*Commentary.*

For real x and y, upper is the square of the sum of the two square roots. For known pure-state overlaps in the unit interval, this is the upper bound in overlap_pra_v3.tex, lines 118–122. The definition is a total real function and does not assume that its arguments lie in that interval.

**Definition 1.2 (The three-state lower bound).**

$$\forall \left(x: \mathbb{R}\right), \left(\forall \left(y: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.lower}\left(x, y\right): \mathbb{R}\right) = \operatorname{ite}\left(\left(\left(1: \mathbb{R}\right) < x + y\right), \left(\operatorname{Real.sqrt}\left(\left(x\right) \cdot \left(y\right)\right) - \operatorname{Real.sqrt}\left(\left(\left(1: \mathbb{R}\right) - x\right) \cdot \left(\left(1: \mathbb{R}\right) - y\right)\right)\right)^{\left(2: \mathbb{N}\right)}, \left(0: \mathbb{R}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.lower` (`✓ std3`).

*Citation.* Ernesto F. Galvão; Daniel J. Brod (2020). *Quantum and classical bounds for two-state overlaps*. DOI: [10.1103/PhysRevA.101.062110](https://doi.org/10.1103/PhysRevA.101.062110). URL: <https://arxiv.org/abs/1902.11039v3>.

*Commentary.*

The lower bound is the square of the difference of the two square roots when x + y is strictly greater than one, and zero otherwise, including x + y = 1. This is the piecewise bound in overlap_pra_v3.tex, lines 125–131, extended as a total function on all real arguments.

**Definition 1.3 (Squared overlap of two vectors).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(u: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right), \left(\forall \left(v: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.overlap}\left(u, v\right): \mathbb{R}\right) = \left(\left\lVert \operatorname{inner}\left(\mathbb{C}, u, v\right) \right\rVert\right)^{\left(2: \mathbb{N}\right)}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.overlap` (`✓ std3`).

*Citation.* Ernesto F. Galvão; Daniel J. Brod (2020). *Quantum and classical bounds for two-state overlaps*. DOI: [10.1103/PhysRevA.101.062110](https://doi.org/10.1103/PhysRevA.101.062110). URL: <https://arxiv.org/abs/1902.11039v3>.

*Commentary.*

The overlap is the squared norm of the complex inner product of u and v in the n-dimensional complex Euclidean space. For unit vectors this is the pure-state overlap of overlap_pra_v3.tex, lines 97–102. The definition itself imposes no normalization condition and includes dimension zero.

**Definition 1.4 (Realizing the given pairs).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(i_{0}: \operatorname{Fin}\left(m\right)\right), \left(\forall \left(j_{0}: \operatorname{Fin}\left(m\right)\right), \left(\forall \left(r: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\forall \left(\psi: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.realizes}\left(i_{0}, j_{0}, r, \psi\right)\right) \Leftrightarrow \left(\left(\forall \left(k: \operatorname{Fin}\left(m\right)\right), \left(\left\lVert \psi\left(k\right) \right\rVert = \left(1: \mathbb{R}\right)\right)\right) \land \left(\forall \left(i: \operatorname{Fin}\left(m\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(m\right)\right), \left(\left(i \ne j\right) \to \left(\left(\left(\{i, j\}: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right)\right) \ne \left(\{i_{0}, j_{0}\}: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right)\right)\right) \to \left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.overlap}\left(\psi\left(i\right), \psi\left(j\right)\right) = r\left(i, j\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.realizes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ernesto F. Galvão; Daniel J. Brod (2020). *Quantum and classical bounds for two-state overlaps*. DOI: [10.1103/PhysRevA.101.062110](https://doi.org/10.1103/PhysRevA.101.062110). URL: <https://arxiv.org/abs/1902.11039v3>.

*Commentary.*

A family ψ realizes the given values when each vector has norm one and every ordered pair of distinct indices has overlap r i j, except when its unordered two-element finite set equals the unknown pair. Thus both orientations of the unknown pair are omitted, and diagonal values of r impose no conditions. The predicate permits arbitrary n, m, i₀, j₀ and r, without separately requiring symmetry of r or distinctness of i₀ and j₀.

**Definition 1.5 (All feasible values of the unknown overlap).**

$$\forall \left(m: \mathbb{N}\right), \left(\forall \left(i_{0}: \operatorname{Fin}\left(m\right)\right), \left(\forall \left(j_{0}: \operatorname{Fin}\left(m\right)\right), \left(\forall \left(r: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.feasible}\left(m, i_{0}, j_{0}, r\right): \operatorname{Set}\left(\mathbb{R}\right)\right) = \{\left(t: \mathbb{R}\right) \mid \left(\exists \left(n: \mathbb{N}\right), \left(\exists \left(\psi: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.realizes}\left(i_{0}, j_{0}, r, \psi\right)\right) \land \left(t = \operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.overlap}\left(\psi\left(i_{0}\right), \psi\left(j_{0}\right)\right)\right)\right)\right)\right)\}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.feasible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ernesto F. Galvão; Daniel J. Brod (2020). *Quantum and classical bounds for two-state overlaps*. DOI: [10.1103/PhysRevA.101.062110](https://doi.org/10.1103/PhysRevA.101.062110). URL: <https://arxiv.org/abs/1902.11039v3>.

*Commentary.*

The feasible set consists of the real values t realized as the unknown squared overlap by some normalized family satisfying every given pair. Both the natural dimension n and the family ψ are existentially quantified, so no fixed dimension is assumed.

**Definition 1.6 (Intersection of the lower bounds).**

$$\forall \left(m: \mathbb{N}\right), \left(\forall \left(i_{0}: \operatorname{Fin}\left(m\right)\right), \left(\forall \left(j_{0}: \operatorname{Fin}\left(m\right)\right), \left(\forall \left(r: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.procLower}\left(m, i_{0}, j_{0}, r\right): \mathbb{R}\right) = \operatorname{sSup}\left(\{\left(t: \mathbb{R}\right) \mid \left(\exists \left(k: \operatorname{Fin}\left(m\right)\right), \left(\left(k \ne i_{0}\right) \land \left(\left(k \ne j_{0}\right) \land \left(t = \operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.lower}\left(r\left(k, i_{0}\right), r\left(k, j_{0}\right)\right)\right)\right)\right)\right)\}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.procLower` (`✓ std3`).

*Citation.* Ernesto F. Galvão; Daniel J. Brod (2020). *Quantum and classical bounds for two-state overlaps*. DOI: [10.1103/PhysRevA.101.062110](https://doi.org/10.1103/PhysRevA.101.062110). URL: <https://arxiv.org/abs/1902.11039v3>.

*Commentary.*

For every k distinct from i₀ and j₀, apply the three-state lower bound to r k i₀ and r k j₀, then take the supremum of the resulting set. This is the lower endpoint of the common-neighbour intersection in overlap_pra_v3.tex, lines 151–154, for a graph with only the pair i₀,j₀ unknown. For m at least three the finite set is nonempty and its supremum is its maximum. The definition also includes smaller m through the real supremum operation.

**Definition 1.7 (Intersection of the upper bounds).**

$$\forall \left(m: \mathbb{N}\right), \left(\forall \left(i_{0}: \operatorname{Fin}\left(m\right)\right), \left(\forall \left(j_{0}: \operatorname{Fin}\left(m\right)\right), \left(\forall \left(r: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.procUpper}\left(m, i_{0}, j_{0}, r\right): \mathbb{R}\right) = \operatorname{sInf}\left(\{\left(t: \mathbb{R}\right) \mid \left(\exists \left(k: \operatorname{Fin}\left(m\right)\right), \left(\left(k \ne i_{0}\right) \land \left(\left(k \ne j_{0}\right) \land \left(t = \operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.upper}\left(r\left(k, i_{0}\right), r\left(k, j_{0}\right)\right)\right)\right)\right)\right)\}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.procUpper` (`✓ std3`).

*Citation.* Ernesto F. Galvão; Daniel J. Brod (2020). *Quantum and classical bounds for two-state overlaps*. DOI: [10.1103/PhysRevA.101.062110](https://doi.org/10.1103/PhysRevA.101.062110). URL: <https://arxiv.org/abs/1902.11039v3>.

*Commentary.*

Apply the three-state upper bound through each common neighbour k and take the infimum of those values. This is the upper endpoint of the intersection in overlap_pra_v3.tex, lines 151–154, for one unknown pair. For m at least three the finite nonempty set has a minimum; the definition uses the real infimum operation for every m.

**Definition 1.8 (Universal tightness with one unknown pair).**

$$\left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.claim}\right) \Leftrightarrow \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(i_{0}: \operatorname{Fin}\left(m\right)\right), \left(\forall \left(j_{0}: \operatorname{Fin}\left(m\right)\right), \left(\forall \left(r: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(\left(3: \mathbb{N}\right) \le m\right) \to \left(\left(i_{0} \ne j_{0}\right) \to \left(\left(\operatorname{Set.Nonempty}\left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.feasible}\left(m, i_{0}, j_{0}, r\right)\right)\right) \to \left(\left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.procLower}\left(m, i_{0}, j_{0}, r\right) = \operatorname{sInf}\left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.feasible}\left(m, i_{0}, j_{0}, r\right)\right)\right) \land \left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.procUpper}\left(m, i_{0}, j_{0}, r\right) = \operatorname{sSup}\left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.feasible}\left(m, i_{0}, j_{0}, r\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ernesto F. Galvão; Daniel J. Brod (2020). *Quantum and classical bounds for two-state overlaps*. DOI: [10.1103/PhysRevA.101.062110](https://doi.org/10.1103/PhysRevA.101.062110). URL: <https://arxiv.org/abs/1902.11039v3>.

*Commentary.*

For every m at least three, every pair of distinct indices i₀,j₀ and every given array r with a nonempty feasible set, claim asserts that procLower equals the feasible infimum and procUpper equals the feasible supremum. This formulates tightness for the case of one unknown pair in the optimality question of overlap_pra_v3.tex, line 165. All other pairs are already given, so revisiting the unknown pair uses the same common-neighbour bounds. The statement concerns pure states in arbitrary finite dimension.

**Theorem 1.9 (Four pure states contradict universal tightness).**

$$\neg \left(\operatorname{D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/galvao-brod-2020-overlap-interval-propagation` (refuted) by `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"galvao-brod-2020-overlap-interval-propagation","declaration_gid":"D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ernesto F. Galvão; Daniel J. Brod (2020). *Quantum and classical bounds for two-state overlaps*. DOI: [10.1103/PhysRevA.101.062110](https://doi.org/10.1103/PhysRevA.101.062110). URL: <https://arxiv.org/abs/1902.11039v3>.

*Commentary.*

Take m = 4, i₀ = 2 and j₀ = 3. Let the rows of r be (1,0,1/2,1/2), (0,1,1/2,0), (1/2,1/2,1,0) and (1/2,0,0,1). The entries at the unknown pair impose no condition. The two common neighbours are 0 and 1. Through 0 the lower bound is lower (1/2) (1/2) = 0, because the sum equals one; through 1 it is lower (1/2) 0 = 0. The set defining procLower is therefore the singleton containing zero, and procLower 4 2 3 r = 0.

Put q = √(1/2) and choose ψ 0 = (1,0,0), ψ 1 = (0,1,0), ψ 2 = (q,q,0) and ψ 3 = (q,0,q) in complex Euclidean dimension three, including each real q as a complex scalar. Since q² = 1/2 and its complex norm squared is also 1/2, summing squared coordinate norms gives norm one for every vector. Expanding each inner product as the sum of the three conjugate-coordinate products gives overlap (ψ 0) (ψ 1) = 0, overlap (ψ 0) (ψ 2) = overlap (ψ 0) (ψ 3) = overlap (ψ 1) (ψ 2) = 1/2, and overlap (ψ 1) (ψ 3) = 0, with the same values in reverse order. Thus this family realizes r.

Next let a, b and c be unit vectors in any finite complex Euclidean dimension, with overlap a b = 0 and overlap a c = overlap b c = 1/2. The zero squared norm of the inner product of a and b makes them orthogonal. Set p = ⟨a,c⟩ a + ⟨b,c⟩ b, using the inner product linear in its second argument. The two summands are orthogonal, and their squared norms add to 1/2 + 1/2 = 1, so the squared norm of p is one. Conjugate symmetry also gives Re ⟨c,p⟩ = |⟨a,c⟩|² + |⟨b,c⟩|² = 1. The equality criterion relating the norm and the real inner product, together with the unit norm of c, gives c = p.

Apply this identity to a = ψ 0, b = ψ 1 and c = ψ 2 in an arbitrary realization, and put d = ψ 3. The given zero overlap of b and d gives ⟨b,d⟩ = 0. Expanding the first argument using c = ⟨a,c⟩ a + ⟨b,c⟩ b therefore gives ⟨c,d⟩ = conjugate(⟨a,c⟩) ⟨a,d⟩. Multiplicativity of the complex norm and invariance under conjugation yield overlap c d = |⟨a,c⟩|² |⟨a,d⟩|² = (1/2)(1/2) = 1/4.

The explicit family in dimension three makes the feasible set nonempty. The identity just proved shows that every feasible value is 1/4, and the explicit family attains that value. Hence the feasible set is the singleton containing 1/4, whose infimum is 1/4. If claim held, its lower-endpoint equality at m = 4, i₀ = 2, j₀ = 3 and this r would give 0 = 1/4, a contradiction. This already disproves the conjunction of endpoint equalities without computing procUpper.

## References

- Truth anchor: `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.claim`
- Truth anchor: `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.feasible`
- Truth anchor: `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.lower`
- Truth anchor: `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.overlap`
- Truth anchor: `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.procLower`
- Truth anchor: `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.procUpper`
- Truth anchor: `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.realizes`
- Truth anchor: `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.result`
- Truth anchor: `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.upper`
