# Weak Abelian Borders and Question 2

## Abstract

Weak abelian borders, bounded periodicity, and the geometric conditions of Question 2.

**Definition 1.1 (Letter counts).**

$$letterCount\left(u, a\right) = count\left(u, a\right)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.letterCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

For words over Fin(k), letterCount(u,a) is the number of occurrences of a in u.

**Definition 1.2 (Equal letter frequencies).**

$$WeakAbelianEquiv\left(u, v\right) \Leftrightarrow \left(u \ne [] \land \left(v \ne [] \land \left(\forall a \in Fin\left(k\right),\; length\left(v\right) \cdot letterCount\left(u, a\right) = length\left(u\right) \cdot letterCount\left(v, a\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.WeakAbelianEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

Two nonempty words are weakly abelian equivalent when every letter has the same frequency in both words. Cross multiplication avoids division by their positive lengths.

**Definition 1.3 (Weak abelian borders).**

$$WeakAbelianBordered\left(u\right) \Leftrightarrow \left(\exists r \in Nat,\; \exists s \in Nat,\; 1 \le r \land \left(r < length\left(u\right) \land \left(1 \le s \land \left(s \le length\left(u\right) \land WeakAbelianEquiv\left(take\left(r, u\right), drop\left(length\left(u\right) - s, u\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.WeakAbelianBordered` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

A border consists of a nonempty proper prefix and a nonempty suffix with equal letter frequencies. The suffix may be the entire word; overlaps between the prefix and suffix are permitted.

**Definition 1.4 (Contiguous factors).**

$$factor\left(w, i, n\right) = map\left(j \mapsto w\left(i + j\right), range\left(n\right)\right)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.factor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

The factor starting at i with length n is the list of letters w(i), w(i+1), through w(i+n-1). The length-zero factor is empty.

**Definition 1.5 (Bounded weak abelian periodicity).**

$$BoundedWeakAbelianPeriodic\left(w\right) \Leftrightarrow \left(\exists t \in Nat\to Nat,\; \exists C \in Nat,\; StrictMono\left(t\right) \land \left(\left(\forall i \in Nat,\; t\left(i + 1\right) - t\left(i\right) \le C\right) \land \left(\forall i \in Nat,\; WeakAbelianEquiv\left(factor\left(w, t\left(i\right), t\left(i + 1\right) - t\left(i\right)\right), factor\left(w, t\left(0\right), t\left(1\right) - t\left(0\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.BoundedWeakAbelianPeriodic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

After the finite prefix of length t(0), the strictly increasing cuts t partition the word into nonempty blocks of length at most C. Every block has the letter frequencies of the first block.

**Definition 1.6 (Prefix Parikh vectors).**

$$\forall a \in Fin\left(k\right),\; coordinate\left(parikhPoint\left(w, n\right), a\right) = castReal\left(letterCount\left(factor\left(w, 0, n\right), a\right)\right)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.parikhPoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

The point parikhPoint(w,n) in Euclidean k-space records the counts of each letter in the prefix of length n, viewed as real coordinates.

**Definition 1.7 (The continuous polygonal graph).**

$$graph\left(w\right) = iUnion\left(n \mapsto segment\left(parikhPoint\left(w, n\right), parikhPoint\left(w, n + 1\right)\right)\right)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.graph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

The graph is the union, for all natural n, of the closed segments joining consecutive prefix Parikh vectors. It contains the full polygonal path, including points between cuts.

**Definition 1.8 (An affine line).**

$$line\left(x0, a\right) = \{ x: EuclideanSpace\left(Real, Fin\left(k\right)\right) \mid \exists t \in Real,\; x = x0 + t \cdot a\} $$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.line` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

The line through x0 in direction a consists of all x0+t a for real t.

**Definition 1.9 (Rational directions).**

$$RationalDirection\left(a\right) \Leftrightarrow \left(a \ne 0 \land \left(\forall i \in Fin\left(k\right),\; \exists q \in Rat,\; coordinate\left(a, i\right) = castReal\left(q\right)\right)\right)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.RationalDirection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

A rational direction is a nonzero vector all of whose coordinates are rational numbers.

**Definition 1.10 (Tangential lines).**

$$IsTangentialLine\left(w, a, y\right) \Leftrightarrow \left(\exists b \in EuclideanSpace\left(Real, Fin\left(k\right)\right),\; \exists d \in Real,\; b \ne 0 \land \left(inner\left(b, a\right) = 0 \land \left(\left(\forall x \in EuclideanSpace\left(Real, Fin\left(k\right)\right),\; x \in graph\left(w\right) \Rightarrow d \le inner\left(b, x\right)\right) \land \left(\left(\exists x \in EuclideanSpace\left(Real, Fin\left(k\right)\right),\; x \in graph\left(w\right) \land inner\left(b, x\right) = d\right) \land \left(Subset\left(line\left(y, a\right), \{ x: EuclideanSpace\left(Real, Fin\left(k\right)\right) \mid inner\left(b, x\right) = d\} \right) \land \left(\forall x \in EuclideanSpace\left(Real, Fin\left(k\right)\right),\; x \in graph\left(w\right) \Rightarrow \left(inner\left(b, x\right) = d \Rightarrow x \in line\left(y, a\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.IsTangentialLine` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

A nonzero normal b orthogonal to a defines a supporting hyperplane at height d. The graph meets that hyperplane, and every point of contact lies on the single axis-parallel line through y, which itself lies in the hyperplane.

**Definition 1.11 (Cylinder containment and bounded tangential gaps).**

$$GeometricHypotheses\left(w\right) \Leftrightarrow \left(\exists x0 \in EuclideanSpace\left(Real, Fin\left(k\right)\right),\; \exists a \in EuclideanSpace\left(Real, Fin\left(k\right)\right),\; \exists M \in Real,\; RationalDirection\left(a\right) \land \left(\left(\forall x \in EuclideanSpace\left(Real, Fin\left(k\right)\right),\; x \in graph\left(w\right) \Rightarrow infDist\left(x, line\left(x0, a\right)\right) \le M\right) \land \left(\forall y \in EuclideanSpace\left(Real, Fin\left(k\right)\right),\; IsTangentialLine\left(w, a, y\right) \Rightarrow \left(\exists D \in Nat,\; \forall n \in Nat,\; \exists m \in Nat,\; n \le m \land \left(m \le n + D \land parikhPoint\left(w, m\right) \in line\left(y, a\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.GeometricHypotheses` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

The entire graph stays at distance at most M from a line with rational direction. For each tangential line there is a natural D such that every index window from n through n+D contains a cut point on that line; D may depend on the line.

**Definition 1.12 (The positive answer to Question 2).**

$$claim \Leftrightarrow \left(\forall k \in Nat,\; \forall w \in Nat\to Fin\left(k\right),\; BoundedWeakAbelianPeriodic\left(w\right) \Rightarrow \left(GeometricHypotheses\left(w\right) \Rightarrow Finite\left(\{ u: List\left(Fin\left(k\right)\right) \mid \left(\exists i \in Nat,\; \exists n \in Nat,\; u = factor\left(w, i, n\right)\right) \land \left(u \ne [] \land \left(\neg (WeakAbelianBordered\left(u\right))\right)\right)\} \right)\right)\right)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

Question 2 asks whether bounded weak abelian periodicity, cylinder containment with rational axis, and bounded gaps on each tangential line imply that only finitely many nonempty factors are weakly abelian unbordered. The border convention allows a whole-word suffix, so its finiteness conclusion is also implied by the positive answer under a proper-suffix convention.

## References

- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.BoundedWeakAbelianPeriodic`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.GeometricHypotheses`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.IsTangentialLine`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.RationalDirection`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.WeakAbelianBordered`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.WeakAbelianEquiv`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.claim`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.factor`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.graph`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.letterCount`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.line`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.parikhPoint`
