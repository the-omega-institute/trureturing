# The printed Chen–Chow conjecture for membranes

## Abstract

A normalized two-letter array satisfies the printed membrane shuffle equations and has no piecewise bilinear realization.

**Definition 1.1 (Ambient plane).**

$$\operatorname{Plane} = \mathbb{R} \times \mathbb{R}$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Plane` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A point pairs a real row coordinate with a real column coordinate.

**Definition 1.2 (Unit interval).**

$$\operatorname{UnitInterval} = [0, 1]$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.UnitInterval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both endpoints belong to the interval.

**Definition 1.3 (Unit square).**

$$\operatorname{UnitSquare} = \operatorname{UnitInterval} \times \operatorname{UnitInterval}$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.UnitSquare` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The square is the product of the two closed unit intervals.

**Definition 1.4 (Ambient membrane type).**

$$\forall d \in \mathbb{N},\; \operatorname{Membrane}\left(d\right) = \left(\mathbb{R} \to \left(\mathbb{R} \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{R}\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Membrane` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function takes row coordinate, column coordinate and component, in that order.

**Definition 1.5 (Uniform grid point).**

$$\forall m \in \mathbb{N}, i \in \mathbb{N},\; \operatorname{gridPoint}\left(m, i\right) = \frac{\operatorname{cast}\left(i, \mathbb{R}\right)}{\operatorname{cast}\left(m, \mathbb{R}\right)}$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.gridPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Division uses Lean's total real division. The grid predicate below chooses positive grid sizes.

**Definition 1.6 (Open grid strip).**

$$\forall m \in \mathbb{N}, i \in \operatorname{Fin}\left(m\right),\; \operatorname{openStrip}\left(m, i\right) = (\operatorname{gridPoint}\left(m, \operatorname{val}\left(i\right)\right), \operatorname{gridPoint}\left(m, \operatorname{val}\left(i\right) + 1\right))$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.openStrip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The endpoints are excluded.

**Definition 1.7 (Closed grid strip).**

$$\forall m \in \mathbb{N}, i \in \operatorname{Fin}\left(m\right),\; \operatorname{closedStrip}\left(m, i\right) = [\operatorname{gridPoint}\left(m, \operatorname{val}\left(i\right)\right), \operatorname{gridPoint}\left(m, \operatorname{val}\left(i\right) + 1\right)]$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.closedStrip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The endpoints are included.

**Definition 1.8 (Piecewise bilinear membranes).**

$$\forall d \in \mathbb{N}, X \in \operatorname{Membrane}\left(d\right),\; \operatorname{PiecewiseBilinear}\left(X\right) \Leftrightarrow (\exists m \in \mathbb{N}, n \in \mathbb{N},\; \left(0 < m \land 0 < n\right) \land (\forall i \in \operatorname{Fin}\left(m\right), j \in \operatorname{Fin}\left(n\right), c \in \operatorname{Fin}\left(d\right),\; \exists a \in \mathbb{R}, b \in \mathbb{R}, e \in \mathbb{R}, f \in \mathbb{R},\; \forall s \in \mathbb{R}, t \in \mathbb{R},\; \left(s \in \operatorname{closedStrip}\left(m, i\right) \land t \in \operatorname{closedStrip}\left(n, j\right)\right) \Rightarrow X\left(s, t, c\right) = a + b \cdot s + e \cdot t + f \cdot s \cdot t))$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.PiecewiseBilinear` (`✓ std3`).

*Citation.* Carlos Améndola; Gabriel Riffo; Leonard Schmitz (2026). *Universal Varieties for Signatures of Membranes*. DOI: [10.48550/arXiv.2610.16724](https://doi.org/10.48550/arXiv.2610.16724). URL: <https://arxiv.org/abs/2610.16724v1>.

*Commentary.*

Section 4, p. 20, uses positive uniform grid sizes and biaffinity on every closed cell. One ambient function supplies the values on both sides of every shared boundary. The conditions constrain its restriction to the unit square.

**Definition 1.9 (Native mixed partial).**

$$\forall d \in \mathbb{N}, X \in \operatorname{Membrane}\left(d\right), c \in \operatorname{Fin}\left(d\right), z \in \operatorname{Plane},\; \operatorname{mixed}\left(X, c, z\right) = \operatorname{deriv}\left((s: \mathbb{R} \mapsto \operatorname{deriv}\left((t: \mathbb{R} \mapsto X\left(s, t, c\right)), z.2\right)), z.1\right)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.mixed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Differentiate the component in the column variable at the second coordinate, then in the row variable at the first coordinate. Both occurrences of deriv denote Lean's total derivative. On an open grid cell the result is the coefficient of the product of the two coordinates.

**Definition 1.10 (Bounded measurable representatives).**

$$\forall d \in \mathbb{N}, f \in \operatorname{Fin}\left(d\right) \to \left(\operatorname{Plane} \to \mathbb{R}\right),\; \operatorname{BoundedMeasurable}\left(f\right) \Leftrightarrow \left((\forall c \in \operatorname{Fin}\left(d\right),\; \operatorname{Measurable}\left(f\left(c\right)\right)) \land (\exists M \in \mathbb{R},\; 0 \le M \land (\forall c \in \operatorname{Fin}\left(d\right), z \in \operatorname{Plane},\; \lvert\lvert f\left(c, z\right)\rvert\rvert \le M))\right)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.BoundedMeasurable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each component is measurable and one nonnegative bound controls all components on the full plane.

**Definition 1.11 (Permutation type).**

$$\forall l \in \mathbb{N},\; \operatorname{Rank}\left(l\right) = \operatorname{Perm}\left(\operatorname{Fin}\left(l\right)\right)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Rank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The degree determines the finite set of slots.

**Definition 1.12 (Insertion permutation on four slots).**

$$\forall p \in \operatorname{Fin}\left(4\right),\; \operatorname{insertionRank}\left(p\right)\left(0\right) = p \land (\forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{insertionRank}\left(p\right)\left(\operatorname{succAbove}\left(0, i\right)\right) = \operatorname{succAbove}\left(p, i\right))$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.insertionRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The permutation takes zero to p. The succAbove map enumerates the remaining slots in order, so these two clauses determine the permutation on all four slots.

**Definition 1.13 (Word type).**

$$\forall d \in \mathbb{N}, l \in \mathbb{N},\; \operatorname{Word}\left(d, l\right) = \left(\operatorname{Fin}\left(l\right) \to \operatorname{Fin}\left(d\right)\right)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A word assigns one letter to each slot.

**Definition 1.14 (Truncated array type).**

$$\forall R \in \operatorname{Type}, d \in \mathbb{N}, k \in \mathbb{N},\; \operatorname{Array}\left(R, d, k\right) = \prod_{l: \operatorname{Fin}\left(k + 1\right)} (\operatorname{Word}\left(d, \operatorname{val}\left(l\right)\right) \to \left(\operatorname{Rank}\left(\operatorname{val}\left(l\right)\right) \to R\right))$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Array` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is a dependent function type. Choosing a finite degree fixes both the word type and the permutation type.

**Definition 1.15 (Block permutation).**

$$\forall m \in \mathbb{N}, n \in \mathbb{N}, a \in \operatorname{Rank}\left(m\right), b \in \operatorname{Rank}\left(n\right),\; (\forall i \in \operatorname{Fin}\left(m\right),\; \operatorname{blockRank}\left(a, b\right)\left(\operatorname{castAdd}\left(n, i\right)\right) = \operatorname{castAdd}\left(n, a\left(i\right)\right)) \land (\forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{blockRank}\left(a, b\right)\left(\operatorname{natAdd}\left(m, j\right)\right) = \operatorname{natAdd}\left(m, b\left(j\right)\right))$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.blockRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

castAdd and natAdd are the two Fin embeddings. The second offsets a slot by the first block's size.

**Definition 1.16 (Block-increasing permutations).**

$$\forall m \in \mathbb{N}, n \in \mathbb{N}, p \in \operatorname{Rank}\left(m + n\right),\; p \in \operatorname{shuffles}\left(m, n\right) \Leftrightarrow \left((\forall i \in \operatorname{Fin}\left(m\right), j \in \operatorname{Fin}\left(m\right),\; i < j \Rightarrow p\left(\operatorname{castAdd}\left(n, i\right)\right) < p\left(\operatorname{castAdd}\left(n, j\right)\right)) \land (\forall i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; i < j \Rightarrow p\left(\operatorname{natAdd}\left(m, i\right)\right) < p\left(\operatorname{natAdd}\left(m, j\right)\right))\right)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.shuffles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set filters all permutations by strict increase on each block separately.

**Definition 1.17 (Sum over pairs of shuffles).**

$$\forall R \in \operatorname{Type},\; [\operatorname{AddCommMonoid}\left(R\right)],\;\forall d \in \mathbb{N}, m \in \mathbb{N}, n \in \mathbb{N}, s \in \operatorname{Word}\left(d, m + n\right) \to \left(\operatorname{Rank}\left(m + n\right) \to R\right), u \in \operatorname{Word}\left(d, m\right), v \in \operatorname{Word}\left(d, n\right), b \in \operatorname{Rank}\left(m + n\right),\; \operatorname{shuffleSum}\left(s, u, v, b\right) = \sum_{(p, q) \in \operatorname{shuffles}\left(m, n\right) \times \operatorname{shuffles}\left(m, n\right)} s\left(\operatorname{append}\left(u, v\right) \circ p^{-1}, q \circ b \circ p^{-1}\right)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.shuffleSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first shuffle reorders rows. The second reorders columns. Each pair contributes once, including when other pairs select the same coordinate.

**Definition 1.18 (Right-hand side of the printed shuffle).**

$$\forall R \in \operatorname{Type},\; [\operatorname{AddCommMonoid}\left(R\right)],\;\forall d \in \mathbb{N}, k \in \mathbb{N}, s \in \operatorname{Array}\left(R, d, k\right),\; \forall m \in \operatorname{Fin}\left(k + 1\right), n \in \operatorname{Fin}\left(k + 1\right), h \in (\operatorname{val}\left(m\right) + \operatorname{val}\left(n\right) \le k), u \in \operatorname{Word}\left(d, \operatorname{val}\left(m\right)\right), v \in \operatorname{Word}\left(d, \operatorname{val}\left(n\right)\right), a \in \operatorname{Rank}\left(\operatorname{val}\left(m\right)\right), b \in \operatorname{Rank}\left(\operatorname{val}\left(n\right)\right),\; \operatorname{printedRhs}\left(s, m, n, h, u, v, a, b\right) = \left\{\begin{aligned}s\left(n, v, b\right)&\quad\text{if} \operatorname{val}\left(m\right) = 0\\s\left(m, u, a\right)&\quad\text{if} 0 < \operatorname{val}\left(m\right) \land \operatorname{val}\left(n\right) = 0\\\operatorname{shuffleSum}\left(s\left(\langle\operatorname{val}\left(m\right) + \operatorname{val}\left(n\right), \operatorname{ltSuccOfLe}\left(h\right)\rangle\right), u, v, \operatorname{blockRank}\left(a, b\right)^{-1}\right)&\quad\text{if} 0 < \operatorname{val}\left(m\right) \land 0 < \operatorname{val}\left(n\right)\end{aligned}\right.$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.printedRhs` (`✓ std3`).

*Citation.* Carlos Améndola; Gabriel Riffo; Leonard Schmitz (2026). *Universal Varieties for Signatures of Membranes*. DOI: [10.48550/arXiv.2610.16724](https://doi.org/10.48550/arXiv.2610.16724). URL: <https://arxiv.org/abs/2610.16724v1>.

*Commentary.*

Definition 2.6, p. 5, uses the empty pair as a two-sided unit and inverts the block rank for nonempty inputs. The finite index in the last branch has natural value equal to the sum of the degrees. The supplied bound h gives its strict bound via Nat.lt_succ_of_le.

**Definition 1.19 (The printed truncated shuffle equations).**

$$\forall R \in \operatorname{Type},\; [\operatorname{Semiring}\left(R\right)],\;\forall d \in \mathbb{N}, k \in \mathbb{N}, s \in \operatorname{Array}\left(R, d, k\right),\; \operatorname{Printed}\left(s\right) \Leftrightarrow (\forall m \in \operatorname{Fin}\left(k + 1\right), n \in \operatorname{Fin}\left(k + 1\right), h \in (\operatorname{val}\left(m\right) + \operatorname{val}\left(n\right) \le k), u \in \operatorname{Word}\left(d, \operatorname{val}\left(m\right)\right), v \in \operatorname{Word}\left(d, \operatorname{val}\left(n\right)\right), a \in \operatorname{Rank}\left(\operatorname{val}\left(m\right)\right), b \in \operatorname{Rank}\left(\operatorname{val}\left(n\right)\right),\; s\left(m, u, a\right) \cdot s\left(n, v, b\right) = \operatorname{printedRhs}\left(s, m, n, h, u, v, a, b\right))$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Printed` (`✓ std3`).

*Citation.* Carlos Améndola; Gabriel Riffo; Leonard Schmitz (2026). *Universal Varieties for Signatures of Membranes*. DOI: [10.48550/arXiv.2610.16724](https://doi.org/10.48550/arXiv.2610.16724). URL: <https://arxiv.org/abs/2610.16724v1>.

*Commentary.*

Theorem 2.10, p. 6, uses the product in Definition 2.6. Every ordered pair is tested when its natural degrees sum to at most the cutoff. At cutoff four the pair (3,3) is outside the domain because the natural sum is six. The unit branches apply when either degree is zero, including when both are zero.

**Definition 1.20 (The three-cycle in the witness pair).**

$$\operatorname{cycle231} = \operatorname{swap}\left(0, 2\right) \circ \operatorname{swap}\left(0, 1\right)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.cycle231` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The swaps act on Fin 3, with the rightmost swap first. The one-line form in one-based notation is 231.

**Definition 1.21 (Axis coordinates).**

$$\forall l \in \mathbb{N},\; \operatorname{Axis}\left(l\right) = \left(\operatorname{Fin}\left(l\right) \to \mathbb{R}\right)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Axis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An axis is a tuple of real coordinates of the given degree.

**Definition 1.22 (Paired axis coordinates).**

$$\forall l \in \mathbb{N},\; \operatorname{Axes}\left(l\right) = \operatorname{Axis}\left(l\right) \times \operatorname{Axis}\left(l\right)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Axes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first axis supplies row coordinates and the second supplies column coordinates.

**Definition 1.23 (Unit cube).**

$$\forall l \in \mathbb{N}, x \in \operatorname{Axis}\left(l\right),\; x \in \operatorname{cube}\left(l\right) \Leftrightarrow (\forall i \in \operatorname{Fin}\left(l\right),\; x\left(i\right) \in \operatorname{UnitInterval})$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.cube` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every coordinate belongs to the closed unit interval.

**Definition 1.24 (Weakly increasing unit simplex).**

$$\forall l \in \mathbb{N}, x \in \operatorname{Axis}\left(l\right),\; x \in \operatorname{simplex}\left(l\right) \Leftrightarrow \left(x \in \operatorname{cube}\left(l\right) \land \operatorname{Monotone}\left(x\right)\right)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.simplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entries are weakly increasing in slot order.

**Definition 1.25 (Paired coordinate evaluation).**

$$\forall l \in \mathbb{N}, i \in \operatorname{Fin}\left(l\right), j \in \operatorname{Fin}\left(l\right), z \in \operatorname{Axes}\left(l\right),\; \operatorname{coordinate}\left(i, j, z\right) = (z.1\left(i\right), z.2\left(j\right))$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.coordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two slot indices select coordinates on separate axes.

**Definition 1.26 (Product of paired component evaluations).**

$$\forall d \in \mathbb{N}, l \in \mathbb{N}, f \in \operatorname{Fin}\left(d\right) \to \left(\operatorname{Plane} \to \mathbb{R}\right), w \in \operatorname{Word}\left(d, l\right), r \in \operatorname{Rank}\left(l\right), z \in \operatorname{Axes}\left(l\right),\; \operatorname{integrand}\left(f, w, r, z\right) = \prod_{i: \operatorname{Fin}\left(l\right)} f\left(w\left(i\right), \operatorname{coordinate}\left(i, r\left(i\right), z\right)\right)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.integrand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The word selects the component. The rank permutes the slots of the column axis.

**Definition 1.27 (Integral over the two simplices).**

$$\forall d \in \mathbb{N}, l \in \mathbb{N}, f \in \operatorname{Fin}\left(d\right) \to \left(\operatorname{Plane} \to \mathbb{R}\right), w \in \operatorname{Word}\left(d, l\right), r \in \operatorname{Rank}\left(l\right),\; \operatorname{simplexIntegral}\left(f, w, r\right) = \int_{\operatorname{simplex}\left(l\right) \times \operatorname{simplex}\left(l\right)} \operatorname{integrand}\left(f, w, r, z\right)\,dz$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.simplexIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The measure is Lean's volume on the product of real coordinate spaces, restricted to the two simplices.

**Definition 1.28 (Native mixed-partial signature).**

$$\forall d \in \mathbb{N}, k \in \mathbb{N}, X \in \operatorname{Membrane}\left(d\right), l \in \operatorname{Fin}\left(k + 1\right), w \in \operatorname{Word}\left(d, \operatorname{val}\left(l\right)\right), r \in \operatorname{Rank}\left(\operatorname{val}\left(l\right)\right),\; \operatorname{signature}\left(X, l, w, r\right) = \left\{\begin{aligned}1&\quad\text{if} \operatorname{val}\left(l\right) = 0\\\int_{\operatorname{simplex}\left(\operatorname{val}\left(l\right)\right) \times \operatorname{simplex}\left(\operatorname{val}\left(l\right)\right)} \operatorname{integrand}\left(\operatorname{mixed}\left(X\right), w, r, z\right)\,dz&\quad\text{if} 0 < \operatorname{val}\left(l\right)\end{aligned}\right.$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.signature` (`✓ std3`).

*Citation.* Carlos Améndola; Gabriel Riffo; Leonard Schmitz (2026). *Universal Varieties for Signatures of Membranes*. DOI: [10.48550/arXiv.2610.16724](https://doi.org/10.48550/arXiv.2610.16724). URL: <https://arxiv.org/abs/2610.16724v1>.

*Commentary.*

Definition 1.1, p. 2, uses the two weakly increasing unit simplices and assigns one to the empty coordinate. The coordinate integrand evaluates the real mixed partial at row slot j and column slot r(j). The integral is independent of the ambient extension of an eligible square membrane.

**Definition 1.29 (Realization by a piecewise bilinear membrane).**

$$\forall d \in \mathbb{N}, k \in \mathbb{N}, s \in \operatorname{Array}\left(\mathbb{R}, d, k\right),\; \operatorname{Realizes}\left(s\right) \Leftrightarrow \left(\exists X \in \operatorname{Membrane}\left(d\right),\; \operatorname{PiecewiseBilinear}\left(X\right) \land \operatorname{signature}\left(X\right) = s\right)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Realizes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Signature equality is equality of the entire truncated array.

**Definition 1.30 (Conjecture 6.10 as printed).**

$$\forall d \in \mathbb{N}, k \in \mathbb{N},\; 2 \le d \Rightarrow (\forall s \in \operatorname{Array}\left(\mathbb{R}, d, k\right),\; \operatorname{Printed}\left(s\right) \Rightarrow \operatorname{Realizes}\left(s\right))$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.claim` (`✓ std3`).

*Citation.* Carlos Améndola; Gabriel Riffo; Leonard Schmitz (2026). *Universal Varieties for Signatures of Membranes*. DOI: [10.48550/arXiv.2610.16724](https://doi.org/10.48550/arXiv.2610.16724). URL: <https://arxiv.org/abs/2610.16724v1>.

*Commentary.*

Conjecture 6.10, p. 32. “For every sequence s ∈ ⊕_{ℓ=0}^k ⊕_{ν∈Σ_ℓ}(ℝ^d)^{⊗ℓ} with entries satisfying the two-parameter shuffle identity (Theorem 2.10) there is a piecewise bilinear membrane such that its k-truncated signature coincides with s.” Equality is at every degree, word and permutation in the truncation.

**Definition 1.31 (One-based decimal permutation code).**

$$\forall l \in \mathbb{N}, r \in \operatorname{Rank}\left(l\right),\; \operatorname{rankCode}\left(r\right) = \sum_{i: \operatorname{Fin}\left(l\right)} \left(\operatorname{val}\left(r\left(i\right)\right) + 1\right) \cdot 10^{l - 1 - \operatorname{val}\left(i\right)}$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.rankCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean folds the one-based entries in slot order by multiplying the accumulator by ten and adding the next entry, starting at zero. The exponent uses natural subtraction. The code of the empty permutation is zero.

**Definition 1.32 (Rational certificate lookup).**

$$\forall q \in \mathbb{N},\; (\operatorname{tableEntry}\left(q\right): \mathbb{Q}) = \operatorname{getD}\left(\operatorname{lookup}\left(q, \left\{\begin{aligned}0 \mapsto 1,\quad1 \mapsto 3,\quad12 \mapsto \frac{7}{4},\quad21 \mapsto \frac{11}{4}\\123 \mapsto \frac{7}{12},\quad132 \mapsto \frac{1}{3},\quad213 \mapsto \frac{1}{3},\quad231 \mapsto \frac{19}{12}\\312 \mapsto \frac{7}{12},\quad321 \mapsto \frac{13}{12},\quad1234 \mapsto \frac{71}{576},\quad1243 \mapsto \frac{55}{576}\\1324 \mapsto \frac{35}{576},\quad1342 \mapsto \frac{19}{576},\quad1423 \mapsto \frac{19}{576},\quad1432 \mapsto \frac{19}{576}\\2134 \mapsto \frac{55}{576},\quad2143 \mapsto \frac{13}{192},\quad2314 \mapsto \frac{19}{576},\quad2341 \mapsto \frac{35}{576}\\2413 \mapsto \frac{1}{192},\quad2431 \mapsto \frac{35}{576},\quad3124 \mapsto \frac{19}{576},\quad3142 \mapsto \frac{1}{192}\\3214 \mapsto \frac{19}{576},\quad3241 \mapsto \frac{35}{576},\quad3412 \mapsto \frac{73}{192},\quad3421 \mapsto \frac{107}{576}\\4123 \mapsto \frac{323}{576},\quad4132 \mapsto \frac{179}{576},\quad4213 \mapsto \frac{179}{576},\quad4231 \mapsto \frac{67}{576}\\4312 \mapsto \frac{251}{576},\quad4321 \mapsto \frac{139}{576}\end{aligned}\right\}\right), 0\right)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.tableEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rows give the nonzero code-to-value assignments in increasing code order. The finite map is indexed by the requested code with default zero.

**Definition 1.33 (Rational truncated array).**

$$\forall l \in \operatorname{Fin}\left(5\right), w \in \operatorname{Word}\left(2, \operatorname{val}\left(l\right)\right), r \in \operatorname{Rank}\left(\operatorname{val}\left(l\right)\right),\; \operatorname{rationalWitness}\left(l, w, r\right) = \left\{\begin{aligned}\operatorname{tableEntry}\left(\operatorname{rankCode}\left(r\right)\right)&\quad\text{if} \forall i \in \operatorname{Fin}\left(\operatorname{val}\left(l\right)\right),\; w\left(i\right) = 0\\0&\quad\text{otherwise}\end{aligned}\right.$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.rationalWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These entries form an Array over the rationals. In the empty degree the condition holds vacuously.

**Definition 1.34 (Constant first-letter word).**

$$\forall d \in \mathbb{N}, l \in \mathbb{N},\; \operatorname{oneWord}\left(d, l\right): \operatorname{Word}\left(d + 1, l\right) = (i: \operatorname{Fin}\left(l\right) \mapsto 0)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.oneWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The alphabet has d+1 letters and its first letter has index zero.

**Definition 1.35 (Real truncated array).**

$$\forall l \in \operatorname{Fin}\left(5\right), w \in \operatorname{Word}\left(2, \operatorname{val}\left(l\right)\right), r \in \operatorname{Rank}\left(\operatorname{val}\left(l\right)\right),\; \operatorname{witness}\left(l, w, r\right) = \operatorname{cast}\left(\operatorname{rationalWitness}\left(l, w, r\right), \mathbb{R}\right)$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.witness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational entries are cast to real numbers coordinate by coordinate.

**Theorem 1.36 (A normalized array with no membrane realization).**

$$\neg (\forall d \in \mathbb{N}, k \in \mathbb{N},\; 2 \le d \Rightarrow (\forall s \in \operatorname{Array}\left(\mathbb{R}, d, k\right),\; \operatorname{Printed}\left(s\right) \Rightarrow \operatorname{Realizes}\left(s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.refute_conjecture_6_10_v1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Carlos Améndola; Gabriel Riffo; Leonard Schmitz (2026). *Universal Varieties for Signatures of Membranes*. DOI: [10.48550/arXiv.2610.16724](https://doi.org/10.48550/arXiv.2610.16724). URL: <https://arxiv.org/abs/2610.16724v1>.

*Commentary.*

Take d = 2 and k = 4. The rational array has 443 coordinates, with the empty coordinate equal to one and zero whenever the word uses the second letter. Its coefficients satisfy all 1,177 ordered equations of the printed system. For the input pair (1,1) and (111,231) in one-based notation, both the product and the printed sum equal 19/4.

In a product of the degree-one and degree-three integrals, insert the singleton at one of four positions on each axis. Up to null ties, the 16 chambers partition the joint domain. Reindexing the axes sends old row slot j to π(j) and its old column slot (α ▷ β)(j) to λ((α ▷ β)(j)). The new row word uses π⁻¹ and the new rank is λ ∘ (α ▷ β) ∘ π⁻¹. For the same rational input pair this forward shuffle sum equals 7/4, so equality to a membrane signature is impossible.

The same array refutes the printed conjecture with explicit degree-zero normalization. Realizability under the genuine shuffle equations remains open.

## References

- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Array`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Axes`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Axis`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.BoundedMeasurable`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Membrane`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.PiecewiseBilinear`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Plane`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Printed`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Rank`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Realizes`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.UnitInterval`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.UnitSquare`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Word`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.blockRank`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.claim`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.closedStrip`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.coordinate`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.cube`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.cycle231`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.gridPoint`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.insertionRank`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.integrand`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.mixed`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.oneWord`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.openStrip`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.printedRhs`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.rankCode`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.rationalWitness`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.refute_conjecture_6_10_v1`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.shuffleSum`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.shuffles`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.signature`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.simplex`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.simplexIntegral`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.tableEntry`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.witness`
- Dependency: [D5/S3/Quantum/Transport/MatrixUnitDyson](../../Quantum/Transport/MatrixUnitDyson.md)
