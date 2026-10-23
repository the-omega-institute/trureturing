# Three-class homomorphism limits

## Abstract

Three-class graph homomorphism densities equal their finite weighting sum.

**Definition 1.1 (Yellow weight).**

$$\forall beta: \mathbb{R}, \forall q: \mathbb{R}, \operatorname{yW}\left(beta, q\right) = \operatorname{Real}.\operatorname{sqrt}\left(beta\right) \cdot q$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.yW` (`✓ std3`).

*Citation.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

Day and Sarkar, §3, p. 4: y(q) = √β q. The yellow class has asymptotic size y(q)n.

**Definition 1.2 (Red weight).**

$$\forall beta: \mathbb{R}, \forall q: \mathbb{R}, \operatorname{rW}\left(beta, q\right) = 1 - \operatorname{Real}.\operatorname{sqrt}\left(1 - beta \cdot \left(1 - q^{2}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.rW` (`✓ std3`).

*Citation.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

Day and Sarkar, §3, p. 4: r(q) = 1 − √(1 − β(1 − q²)). The red class has asymptotic size r(q)n.

**Definition 1.3 (Blue weight).**

$$\forall beta: \mathbb{R}, \forall q: \mathbb{R}, \operatorname{bW}\left(beta, q\right) = \operatorname{Real}.\operatorname{sqrt}\left(1 - beta \cdot \left(1 - q^{2}\right)\right) - \operatorname{Real}.\operatorname{sqrt}\left(beta\right) \cdot q$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.bW` (`✓ std3`).

*Citation.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

Day and Sarkar, §3, p. 4: b(q) = √(1 − β(1 − q²)) − √β q. The blue class has asymptotic size b(q)n.

**Definition 1.4 (Floor-sized classes).**

$$\forall beta: \mathbb{R}, \forall q: \mathbb{R}, \forall n: \mathbb{N}, \forall i: \operatorname{Fin}\left(n\right), \operatorname{vertexClass}\left(beta, q, n, i\right) = \operatorname{ite}(\operatorname{val}\left(i\right) < \operatorname{Nat}.\operatorname{floor}\left(\operatorname{yW}\left(beta, q\right) \cdot (n: \mathbb{R})\right))(1)(\operatorname{ite}(\operatorname{val}\left(i\right) < \operatorname{Nat}.\operatorname{floor}\left(\operatorname{yW}\left(beta, q\right) \cdot (n: \mathbb{R})\right) + \operatorname{Nat}.\operatorname{floor}\left(\operatorname{rW}\left(beta, q\right) \cdot (n: \mathbb{R})\right))(0)(2))$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.vertexClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

Vertices are numbered by Fin n. Yellow has index 1, red index 0 and blue index 2. The first Nat.floor(yW beta q * n) vertices are yellow; the next Nat.floor(rW beta q * n) are red; the rest are blue. Nat.floor is the nonnegative natural floor. The source omits floors in its asymptotic class sizes.

**Definition 1.5 (Allowed class pairs).**

$$\forall a: \operatorname{Fin}\left(3\right), \forall b: \operatorname{Fin}\left(3\right), \operatorname{classAllowed}\left(a, b\right) = \left(\left(a = 1 \land b = 1\right) \lor \left(\left(a = 0 \land b = 0\right) \lor \left(a = 0 \lor b = 0\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.classAllowed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

A pair of yellow classes is allowed. A pair with at least one red class is allowed. Blue–blue and yellow–blue pairs are excluded.

**Definition 1.6 (The finite T graph).**

$$\forall beta: \mathbb{R}, \forall q: \mathbb{R}, \forall n: \mathbb{N}, \forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), (\operatorname{tGraph}\left(beta, q, n\right)).\operatorname{Adj}\left(i, j\right) \Leftrightarrow \left(i \ne j \land \operatorname{classAllowed}\left(\operatorname{vertexClass}\left(beta, q, n, i\right), \operatorname{vertexClass}\left(beta, q, n, j\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.tGraph` (`✓ std3`).

*Citation.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

Day and Sarkar, §2, p. 4, verbatim: “The sets Y_T and R_T both span cliques, while B_T is an independent set. Also, every vertex in R_T is connected to every vertex in Y_T and B_T.” There are no yellow–blue edges. The formula specifies the adjacency relation of the SimpleGraph on Fin n; distinct endpoints exclude loops.

**Definition 1.7 (Labelled homomorphisms).**

$$\forall v: \mathbb{N}, \forall n: \mathbb{N}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(v\right)\right), \forall H: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{homCount}\left(G, H\right) = \operatorname{Nat}.\operatorname{card}\left(\{f: \operatorname{Fin}\left(v\right) \to \operatorname{Fin}\left(n\right) \mid \forall i: \operatorname{Fin}\left(v\right), \forall j: \operatorname{Fin}\left(v\right), G.\operatorname{Adj}\left(i, j\right) \Rightarrow H.\operatorname{Adj}\left(\operatorname{f}\left(i\right), \operatorname{f}\left(j\right)\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.homCount` (`✓ std3`).

*Citation.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

Day and Sarkar, §2, p. 3, verbatim: “A graph homomorphism from G_l to H is a map f:V(G_l)→V(H) such that {f(u),f(w)}∈E(H) for all {u,w}∈E(G_l). We write hom(G_l,H) for the number of homomorphisms from G_l to H.” The vertex sets here are Fin v and Fin n. The subtype counts all adjacency-preserving functions, including noninjective ones.

**Definition 1.8 (The literal asymptotic density).**

$$\forall v: \mathbb{N}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(v\right)\right), \forall beta: \mathbb{R}, \forall q: \mathbb{R}, \operatorname{tDens}\left(G, beta, q\right) = \operatorname{limUnder}\left(\operatorname{Filter}.\operatorname{atTop}, (fun n: \mathbb{N} \mapsto \frac{(\operatorname{homCount}\left(G, \operatorname{tGraph}\left(beta, q, n\right)\right): \mathbb{R})}{(n: \mathbb{R})^{v}})\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.tDens` (`✓ std3`).

*Citation.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

Day and Sarkar, §2, p. 3 define t(G_l,H_n) as lim(n→∞) hom(G_l,H_n)/n^v. The displayed limUnder at Filter.atTop is that limit for the floor-sized T graphs. The integer cardinality and vertex number are coerced to real numbers before division.

**Definition 1.9 (Weight of one class).**

$$\forall beta: \mathbb{R}, \forall q: \mathbb{R}, \forall a: \operatorname{Fin}\left(3\right), \operatorname{colourWeight}\left(beta, q, a\right) = \operatorname{ite}(a = 0)(\operatorname{rW}\left(beta, q\right))(\operatorname{ite}(a = 1)(\operatorname{yW}\left(beta, q\right))(\operatorname{bW}\left(beta, q\right)))$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.colourWeight` (`✓ std3`).

*Citation.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

Class 0 receives r(q), class 1 receives y(q), and class 2 receives b(q), as in the red, yellow and blue sets of §3, pp. 4–5.

**Definition 1.10 (Half-integral weights).**

$$\forall a: \operatorname{Fin}\left(3\right), \operatorname{independentWeight}\left(a\right) = \frac{(\operatorname{val}\left(a\right): \mathbb{R})}{2}$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.independentWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

The three indices 0, 1 and 2 encode the fractional independence weights 0, 1/2 and 1. The natural value of the index is coerced to a real number before division by 2.

**Definition 1.11 (Fractional independence colourings).**

$$\forall v: \mathbb{N}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(v\right)\right), \forall c: \operatorname{Fin}\left(v\right) \to \operatorname{Fin}\left(3\right), \operatorname{admissible}\left(G, c\right) = (\forall i: \operatorname{Fin}\left(v\right), \forall j: \operatorname{Fin}\left(v\right), G.\operatorname{Adj}\left(i, j\right) \Rightarrow \operatorname{independentWeight}\left(\operatorname{c}\left(i\right)\right) + \operatorname{independentWeight}\left(\operatorname{c}\left(j\right)\right) \le 1)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.admissible` (`✓ std3`).

*Citation.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

Day and Sarkar, §2, p. 3, verbatim: “Given a graph G, a function φ:V(G)→[0,1] such that φ(u)+φ(w)≤1 for all {u,w}∈E(G) is known as a fractional independence weighting of G.” Here φ takes the three values 0, 1/2 and 1, represented by c:Fin v→Fin 3.

**Definition 1.12 (The finite weighting sum).**

$$\forall v: \mathbb{N}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(v\right)\right), \forall beta: \mathbb{R}, \forall q: \mathbb{R}, \operatorname{weightingSum}\left(G, beta, q\right) = \sum_{c:\operatorname{Fin}\left(v\right) \to \operatorname{Fin}\left(3\right)}(\operatorname{ite}(\operatorname{admissible}\left(G, c\right))(\prod_{i:\operatorname{Fin}\left(v\right)}\operatorname{colourWeight}\left(beta, q, \operatorname{c}\left(i\right)\right))(0))$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.weightingSum` (`✓ std3`).

*Citation.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

Sum the product of class weights over all half-integral fractional independence weightings. Colourings that violate an edge condition contribute zero. This is the sum in Day and Sarkar's Lemma 1, §3, p. 5 (arXiv v1).

**Theorem 1.13 (Nonnegative weights summing to one).**

$$\forall beta: \mathbb{R}, \forall q: \mathbb{R}, \left(beta \in \operatorname{Set}.\operatorname{Icc}\left(0, 1\right) \land q \in \operatorname{Set}.\operatorname{Icc}\left(0, 1\right)\right) \Rightarrow \left(0 \le \operatorname{yW}\left(beta, q\right) \land \left(0 \le \operatorname{rW}\left(beta, q\right) \land \left(0 \le \operatorname{bW}\left(beta, q\right) \land \operatorname{yW}\left(beta, q\right) + \operatorname{rW}\left(beta, q\right) + \operatorname{bW}\left(beta, q\right) = 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.weights_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

For beta and q in [0,1], the yellow, red and blue weights are nonnegative and sum to one. Their natural floors therefore fit into the n-vertex carrier.

**Theorem 1.14 (Counting the density).**

$$\forall v: \mathbb{N}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(v\right)\right), \forall beta: \mathbb{R}, \forall q: \mathbb{R}, \left(beta \in \operatorname{Set}.\operatorname{Icc}\left(0, 1\right) \land q \in \operatorname{Set}.\operatorname{Icc}\left(0, 1\right)\right) \Rightarrow \operatorname{tDens}\left(G, beta, q\right) = \operatorname{weightingSum}\left(G, beta, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.tDens_eq_weightingSum` (`✓ std3`). ∎

*Citation.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

For every finite labelled SimpleGraph and every beta and q in [0,1], the homomorphism limit equals the weighting sum. The ideal count partitions functions by their class map. A function counted ideally but failing to preserve adjacency identifies the endpoints of an edge. Restricting such a function away from one endpoint gives the bound n^(v−1) for each ordered pair; the total error is at most v² n^(v−1). Dividing by n^v makes this error tend to zero, while each floor-sized class fraction tends to its weight. Nonadjacent vertices may share an image. The argument includes v=0 and zero class weights.

## References

- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.admissible`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.bW`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.classAllowed`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.colourWeight`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.homCount`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.independentWeight`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.rW`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.tDens`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.tDens_eq_weightingSum`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.tGraph`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.vertexClass`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.weightingSum`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.weights_valid`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.yW`
