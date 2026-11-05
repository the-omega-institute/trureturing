# The termwise Mermin local-perception bound

## Abstract

Four positive context tables with shared singleton means obey the sharp termwise Mermin local-perception bound, after exact elimination of the pair moments.

**Definition 1.1 (Finite expectation).**

$$avg\left(p, f\right)=\sum_{i}p_{i}f_{i}$$

*Formalization.* `D5/S3/QuantumBounds/LocalPerceptionMermin.avg` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

The finite sum of p(i) f(i). Normalization and nonnegativity are hypotheses of the bound, not part of this definition.

**Definition 1.2 (Independent context expectation).**

$$avgfour\left(p, q, r, s, f\right)=\sum_{i,j,k,l}p_{i}q_{j}r_{k}s_{l}f\left(i, j, k, l\right)$$

*Formalization.* `D5/S3/QuantumBounds/LocalPerceptionMermin.avg4` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

The fourfold sum with weight p(i) q(j) r(k) s(l). These independently drawn context samples form an auxiliary mathematical construction; no original all-settings joint distribution is assumed.

**Theorem 1.3 (The classical bound for real contractions).**

$$abc-aBC-AbC-ABc\leq2$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/LocalPerceptionMermin.classical_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

For a,A,b,B,c,C in [-1,1], a b c - a B C - A b C - A B c is at most two. The proof interpolates four of the variables between their endpoints and checks the remaining linear bounds. This consumed helper supplies the pointwise inequality in table_bound.

**Definition 1.4 (The tetrahedron of contexts).**

$$e=((0,2,4),(0,3,5),(1,2,5),(1,3,4))$$

*Formalization.* `D5/S3/QuantumBounds/LocalPerceptionMermin.edge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

The four rows label settings A0,B0,C0; A0,B1,C1; A1,B0,C1; A1,B1,C0. Settings have labels 0,1,2,3,4,5 in order A0,A1,B0,B1,C0,C1. Every setting belongs to exactly two contexts.

**Definition 1.5 (The context triple moment).**

$$t_{v}=\sum_{i}p\left(v, i\right)\prod_{j=0}^{2}u\left(v, j, i\right)$$

*Formalization.* `D5/S3/QuantumBounds/LocalPerceptionMermin.triple` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

The expectation of the product of the three bounded outputs in the indicated context.

**Definition 1.6 (Squared marginal weights).**

$$S\left(m, t\right)=(m_{0}m_{2}m_{4})^{2}t_{0}-(m_{0}m_{3}m_{5})^{2}t_{1}-(m_{1}m_{2}m_{5})^{2}t_{2}-(m_{1}m_{3}m_{4})^{2}t_{3}$$

*Formalization.* `D5/S3/QuantumBounds/LocalPerceptionMermin.witness` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

The termwise witness is (m0 m2 m4)^2 t0 - (m0 m3 m5)^2 t1 - (m1 m2 m5)^2 t2 - (m1 m3 m4)^2 t3. For the product observable A tensor B tensor C, Ray Eq. (52) gives b c A, a c B, and a b C, whose tensor product has coefficient (a b c)^2. The signs are those of Eq. (54), included once. Applying the LPO maps to the entire Bell operator before tensoring is a different functional.

**Theorem 1.7 (The universal context-table bound).**

$$S\left(m, t\right)\leq2$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/LocalPerceptionMermin.table_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

Assume four finite nonnegative probability tables of mass one, bounded outputs, and singleton expectations agreeing at repeated setting labels. The squared-weight termwise witness is at most two. No pair of settings repeats across these four contexts, and no additional constraints on pair moments are needed. Independently draw a triple from each table; for every setting multiply the two outcomes in its incident contexts, then multiply by that setting's mean. The resulting six responses lie in [-1,1]. Every selected triple expectation factors into its original triple moment times the square of its three single means. Averaging the classical Mermin inequality proves the bound. The Lean statement is this finite-table result; the quantum consequence follows by the product-effect construction described below.

**Theorem 1.8 (The absolute bound).**

$$|S\left(m, t\right)|\leq2$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/LocalPerceptionMermin.table_abs_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

The same hypotheses give absolute witness at most two. Negating the first output in all contexts and the two Alice means negates every triple moment, while preserving squared weights, and gives the lower bound.

**Definition 1.9 (The retained odd moments).**

$$L=(a+b+c+t,a+b-c-t,a-b+c-t,a-b-c+t)$$

*Formalization.* `D5/S3/QuantumBounds/LocalPerceptionMermin.odd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

The four components are a+b+c+t, a+b-c-t, a-b+c-t, a-b-c+t. They are the odd parts of the eight positivity rows paired under simultaneous outcome reversal.

**Definition 1.10 (The three omitted pair moments).**

$$h=(1+d+e+f,1+d-e-f,1-d+e-f,1-d-e+f)$$

*Formalization.* `D5/S3/QuantumBounds/LocalPerceptionMermin.even` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

For pair moments d,e,f, the four components are 1+d+e+f, 1+d-e-f, 1-d+e-f, 1-d-e+f. Their sum is four.

**Definition 1.11 (Eight positivity rows).**

$$\forall i:h_{i}+L_{i}\geq0\land h_{i}-L_{i}\geq0$$

*Formalization.* `D5/S3/QuantumBounds/LocalPerceptionMermin.positiveRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

For each of the four paired rows, both even(i)+odd(i) and even(i)-odd(i) are nonnegative. Dividing these eight numbers by eight gives a probability table.

**Theorem 1.12 (Exact elimination of pair moments).**

$$(\exists d,e,f:positiveRows\left(a, b, c, t, d, e, f\right))\iff\sum_{i=0}^{3}|L_{i}|\leq4$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/LocalPerceptionMermin.eliminate_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

There exist d,e,f satisfying all eight positivity rows if and only if the sum of the absolute values of the four odd components is at most four. Necessity follows from abs(odd(i)) <= even(i). For sufficiency set H(i)=abs(odd(i))+(4-sum abs(odd))/4, so sum H=4, and recover d,e,f by the inverse Hadamard formulas. This is exact existential elimination, not a constraint obtained by setting the omitted pair moments to zero.

For a finite-dimensional density matrix and local Hermitian contractions, the positive product effects (I+alpha A)/2 tensor (I+beta B)/2 tensor (I+gamma C)/2 have nonnegative expectations, sum to one, and give shared single means. The finite-table theorem therefore proves the unrestricted quantum consequence in any finite dimension, including three qubits and binary POVMs. The matrix-to-table construction is an elementary written consequence, not a separately compiled matrix theorem in this module. The value two is attained by |000><000| with both Alice settings -Z and all Bob/Charlie settings Z; this matrix calculation is written, and its scalar arithmetic is replayed separately. The C3322 bound four is outside this result.

## References

- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionMermin.avg`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionMermin.avg4`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionMermin.classical_bound`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionMermin.edge`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionMermin.eliminate_pairs`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionMermin.even`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionMermin.odd`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionMermin.positiveRows`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionMermin.table_abs_bound`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionMermin.table_bound`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionMermin.triple`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionMermin.witness`
