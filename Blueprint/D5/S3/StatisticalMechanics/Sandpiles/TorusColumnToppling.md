# The toppling count of the n x 1 torus sandpile is A023855(n - 1)

## Abstract

On the n x 1 torus, fill every cell except c[0,0] with 4 grains and topple cells holding at least 4 grains, the grains sent to c[0,0] being lost. For every n at least 2 the process reaches a final state, and every legal toppling sequence ending in a final state has A023855(n - 1) topplings, in whatever order the cells are chosen (OEIS A293452, with the printed index corrected).

**Definition 1.1 (The cells of the n x k torus).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{Cell}\left(n, k\right) = \operatorname{ZMod}\left(n\right) \times \operatorname{ZMod}\left(k\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.Cell` (`✓ std3`).

*Citation.* Joerg Arndt (2017). *OEIS A293452, Triangle T(n,k) read by rows: T(n,k) is the number of iterations to reach a final state for an n X k lattice of sandpiles on a torus according to rules specified in A249872*. URL: <https://oeis.org/A293452>.

*Commentary.*

OEIS A249872: "Let the lattice be c[i,j], 0 <= i,j < n." A293452 uses the n X k torus; the cell c[i,j] is the pair (i, j) of residues modulo n and k.

**Definition 1.2 (The initial configuration).**

$$\forall q \in \operatorname{Cell}\left(n, k\right),\; \operatorname{initial}\left(n, k, q\right) = \operatorname{ite}\left(q = 0, 0, 4\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.initial` (`✓ std3`).

*Citation.* Joerg Arndt (2017). *OEIS A293452, Triangle T(n,k) read by rows: T(n,k) is the number of iterations to reach a final state for an n X k lattice of sandpiles on a torus according to rules specified in A249872*. URL: <https://oeis.org/A293452>.

*Commentary.*

OEIS A249872: "Fill each cell except c[0,0] with 4 grains of sand."

**Definition 1.3 (The four neighbours on the torus).**

$$\operatorname{neighbours}\left(p\right) = [(p_{1} + 1, p_{2}), (p_{1} - 1, p_{2}), (p_{1}, p_{2} + 1), (p_{1}, p_{2} - 1)]$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.neighbours` (`✓ std3`).

*Citation.* Joerg Arndt (2017). *OEIS A293452, Triangle T(n,k) read by rows: T(n,k) is the number of iterations to reach a final state for an n X k lattice of sandpiles on a torus according to rules specified in A249872*. URL: <https://oeis.org/A293452>.

*Commentary.*

The 4 neighbours of a cell on the torus, as a list; on the n x 1 torus the last two are the cell itself.

**Definition 1.4 (One iteration).**

$$\operatorname{topple}\left(c, p, q\right) = c\left(q\right) - \operatorname{ite}\left(q = p, 4, 0\right) + \operatorname{ite}\left(q = 0, 0, \operatorname{count}\left(q, \operatorname{neighbours}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.topple` (`✓ std3`).

*Citation.* Joerg Arndt (2017). *OEIS A293452, Triangle T(n,k) read by rows: T(n,k) is the number of iterations to reach a final state for an n X k lattice of sandpiles on a torus according to rules specified in A249872*. URL: <https://oeis.org/A293452>.

*Commentary.*

OEIS A249872: "Decrement the chosen cell by 4 and increment its 4 neighbors by 1. c[0,0] is never increased, sand grains placed here are lost." A neighbour occurring twice in the list receives two grains.

**Definition 1.5 (The configuration after a toppling sequence).**

$$\operatorname{run}\left(L\right) = \operatorname{foldl}\left(\operatorname{topple}, \operatorname{initial}\left(n, k\right), L\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.run` (`✓ std3`).

*Citation.* Joerg Arndt (2017). *OEIS A293452, Triangle T(n,k) read by rows: T(n,k) is the number of iterations to reach a final state for an n X k lattice of sandpiles on a torus according to rules specified in A249872*. URL: <https://oeis.org/A293452>.

*Commentary.*

The cells of the list L are toppled in order, starting from the initial configuration.

**Definition 1.6 (Legal toppling sequences).**

$$\operatorname{Legal}\left(L\right) \Leftrightarrow (\forall i \in \mathbb{N},\; (i < \operatorname{length}\left(L\right)) \Rightarrow (4 \le \operatorname{run}\left(\operatorname{take}\left(i, L\right)\right)\left(L_{i}\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.Legal` (`✓ std3`).

*Citation.* Joerg Arndt (2017). *OEIS A293452, Triangle T(n,k) read by rows: T(n,k) is the number of iterations to reach a final state for an n X k lattice of sandpiles on a torus according to rules specified in A249872*. URL: <https://oeis.org/A293452>.

*Commentary.*

OEIS A249872: "Find a c[i,j] >= 4." Every cell of the sequence holds at least 4 grains when it is toppled.

**Definition 1.7 (Final states).**

$$\operatorname{Stable}\left(c\right) \Leftrightarrow (\forall q, c\left(q\right) < 4)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.Stable` (`✓ std3`).

*Citation.* Joerg Arndt (2017). *OEIS A293452, Triangle T(n,k) read by rows: T(n,k) is the number of iterations to reach a final state for an n X k lattice of sandpiles on a torus according to rules specified in A249872*. URL: <https://oeis.org/A293452>.

*Commentary.*

OEIS A249872: "Until all c[i,j] < 4".

**Definition 1.8 (OEIS A023855).**

$$\forall m \in \mathbb{N},\; \operatorname{a023855}\left(m\right) = \sum_{j \in \operatorname{Icc}\left(1, \operatorname{NatDiv}\left(m + 1, 2\right)\right)} j \cdot (m + 1 - j)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.a023855` (`✓ std3`).

*Citation.* Joerg Arndt (2017). *OEIS A293452, Triangle T(n,k) read by rows: T(n,k) is the number of iterations to reach a final state for an n X k lattice of sandpiles on a torus according to rules specified in A249872*. URL: <https://oeis.org/A293452>.

*Commentary.*

OEIS A023855: "a(n) = 1*(n) + 2*(n-1) + 3*(n-2) + ... + (n+1-k)*k, where k = floor((n+1)/2)."

**Definition 1.9 (The conjecture of OEIS A293452, index corrected).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow ((\exists L \in \operatorname{List}\left(\operatorname{Cell}\left(n, 1\right)\right),\; (\operatorname{Legal}\left(L\right)) \land (\operatorname{Stable}\left(\operatorname{run}\left(L\right)\right))) \land (\forall L \in \operatorname{List}\left(\operatorname{Cell}\left(n, 1\right)\right),\; (\operatorname{Legal}\left(L\right)) \Rightarrow ((\operatorname{Stable}\left(\operatorname{run}\left(L\right)\right)) \Rightarrow (\operatorname{length}\left(L\right) = \operatorname{a023855}\left(n - 1\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.claim` (`✓ std3`).

*Citation.* Joerg Arndt (2017). *OEIS A293452, Triangle T(n,k) read by rows: T(n,k) is the number of iterations to reach a final state for an n X k lattice of sandpiles on a torus according to rules specified in A249872*. URL: <https://oeis.org/A293452>.

*Commentary.*

OEIS A293452, FORMULA: "Conjecture: T(n,1) = A023855(n)." The printed index is off by one: T(1,1) = 0 while A023855(1) = 1, and the column T(n,1) = 0, 1, 2, 7, 10, 22, ... of the entry is A023855 shifted by one place. The claim is the corrected identity T(n,1) = A023855(n - 1) for n at least 2, with T(n,1) the length of every legal toppling sequence that ends in a final state ("According to Knuth, it does not matter which cell is chosen"), together with the existence of such a sequence.

**Theorem 1.10 (Least action and the discrete maximum principle).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.result` (`✓ std3`). ∎

*Resolves.* `Problems/arndt-2017-a293452-torus-column-sandpile` (proved) by `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"arndt-2017-a293452-torus-column-sandpile","declaration_gid":"D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joerg Arndt (2017). *OEIS A293452, Triangle T(n,k) read by rows: T(n,k) is the number of iterations to reach a final state for an n X k lattice of sandpiles on a torus according to rules specified in A249872*. URL: <https://oeis.org/A293452>.

*Commentary.*

Write v(i) for the number of topplings of the cell (i, 0) in a legal sequence. Each toppling of (i, 0) removes 4 grains and returns 2 through the two self-neighbours, so every cell (i, 0) other than c[0,0] holds 4 - 2 v(i) + v(i - 1) + v(i + 1) grains, and the cell c[0,0] is never toppled. Let u(x) = (x(n - x) + [n even] min(x, n - x)) / 2 for 0 <= x <= n; its final configuration 4 - 2 u(x) + u(x - 1) + u(x + 1) is 3 at every cell other than c[0,0] (1 <= x < n), except 2 at x = n/2 when n is even. Least action: along a legal sequence v stays below u, because a cell with v(x) = u(x) holds at most 3 grains and cannot be toppled; hence every legal sequence has at most the sum of u topplings, and a sequence of maximal length ends in a final state. Maximum principle: if a legal sequence ends in a final state, the defect d = u - v is nonnegative, vanishes at x = 0 and x = n, and satisfies d(x - 1) + d(x + 1) - 2 d(x) >= 0 except >= -1 at x = n/2; at the leftmost and the rightmost maximum of d these inequalities fail unless d = 0. So every such sequence has the sum of u topplings, which is the sum over 1 <= j <= floor(n/2) of j (n - j), that is A023855(n - 1).

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.Cell`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.Legal`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.Stable`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.a023855`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.neighbours`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.result`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.run`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.topple`
