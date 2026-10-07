# Packing Domatic Colourings of Paths

## Abstract

Packing colourings and broadcast domination on finite paths.

**Definition 1.1 (Packing and broadcast domination).**

$$IsPackingDomatic\left(n, k, t, f\right) \Leftrightarrow \left(\left(\forall v \in Fin\left(n\right),\; 1 \le f\left(v\right) \land f\left(v\right) \le t\right) \land \left(\left(\forall u \in Fin\left(n\right),\; \forall v \in Fin\left(n\right),\; u \ne v \Rightarrow \left(f\left(u\right) = f\left(v\right) \Rightarrow f\left(u\right) < d\left(u, v\right)\right)\right) \land \left(\exists A \in Fin\left(n\right) \to Fin\left(k\right),\; \forall i \in Fin\left(k\right),\; \forall x \in Fin\left(n\right),\; \exists a \in Fin\left(n\right),\; A\left(a\right) = i \land d\left(x, a\right) \le f\left(a\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PackingDomatic/PackingDomaticPathDefs.IsPackingDomatic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Boštjan Brešar, Jasmina Ferme, Wenjie Hu (2026). *Partitioning an S-packing coloring into broadcast dominating sets*. DOI: [10.48550/arXiv.2610.03477](https://doi.org/10.48550/arXiv.2610.03477). URL: <https://arxiv.org/abs/2610.03477v1>.

*Commentary.*

The path P_n has vertices 0 through n-1 and distance d(u,v)=|u-v|. A colouring f uses the integers 1 through t. Distinct vertices of the same colour j have distance greater than j. A map A partitions the vertices into k classes: for every class i and every vertex x, some vertex a in class i satisfies d(x,a) at most f(a).

**Definition 1.2 (The proposed palette bound).**

$$claim \Leftrightarrow \left(\forall k \in Nat,\; \forall n \in Nat,\; 3 \le k \Rightarrow \left(2 \cdot k \le n \Rightarrow \left(\exists f \in Fin\left(n\right) \to Nat,\; IsPackingDomatic\left(n, k, k + 1, f\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PackingDomatic/PackingDomaticPathDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Boštjan Brešar, Jasmina Ferme, Wenjie Hu (2026). *Partitioning an S-packing coloring into broadcast dominating sets*. DOI: [10.48550/arXiv.2610.03477](https://doi.org/10.48550/arXiv.2610.03477). URL: <https://arxiv.org/abs/2610.03477v1>.

*Commentary.*

Problem 2 asks whether every path P_n with k at least 3 and n at least 2k has a packing k-domatic colouring using at most k+1 colours. Equivalently, it asks whether the packing k-domatic chromatic number of each such path is at most k+1.

## References

- Truth anchor: `D5/S3/Combinatorics/PackingDomatic/PackingDomaticPathDefs.IsPackingDomatic`
- Truth anchor: `D5/S3/Combinatorics/PackingDomatic/PackingDomaticPathDefs.claim`
