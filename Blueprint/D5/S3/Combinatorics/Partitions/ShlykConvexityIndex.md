# Eventual existence of every partition convexity index

## Abstract

Every integer index at least two occurs at every sufficiently large partition total.

**Theorem 1.1 (Exact convexity index at all sufficiently large totals).**

$$\forall k \in \mathbb{N},\; ((2 \le k) \Rightarrow (\exists N \in \mathbb{N},\; (\forall n \in \mathbb{N},\; ((N < n) \Rightarrow (\exists x \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; ((\sum_{s: \operatorname{Fin}\left(n\right)} ((\operatorname{val}\left(s\right) + 1) \cdot x\left(s\right)) = n) \land ((\exists y \in \operatorname{Fin}\left(k\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{N}\right),\; (\exists w \in \operatorname{Fin}\left(k\right) \to \mathbb{R},\; ((\forall i \in \operatorname{Fin}\left(k\right),\; (\forall j \in \operatorname{Fin}\left(k\right),\; ((y\left(i\right) = y\left(j\right)) \Rightarrow (i = j)))) \land ((\forall j \in \operatorname{Fin}\left(k\right),\; (y\left(j\right) \ne x)) \land ((\forall j \in \operatorname{Fin}\left(k\right),\; (\sum_{s: \operatorname{Fin}\left(n\right)} ((\operatorname{val}\left(s\right) + 1) \cdot y\left(j\right)\left(s\right)) = n)) \land ((\forall j \in \operatorname{Fin}\left(k\right),\; (0 < w\left(j\right))) \land ((\sum_{j: \operatorname{Fin}\left(k\right)} (w\left(j\right)) = 1) \land (\forall s \in \operatorname{Fin}\left(n\right),\; ((x\left(s\right): \mathbb{R}) = \sum_{j: \operatorname{Fin}\left(k\right)} (w\left(j\right) \cdot (y\left(j\right)\left(s\right): \mathbb{R}))))))))))) \land (\forall r \in \mathbb{N},\; (\forall z \in \operatorname{Fin}\left(r\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{N}\right),\; (\forall v \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; ((\forall i \in \operatorname{Fin}\left(r\right),\; (\forall j \in \operatorname{Fin}\left(r\right),\; ((z\left(i\right) = z\left(j\right)) \Rightarrow (i = j)))) \Rightarrow ((\forall j \in \operatorname{Fin}\left(r\right),\; (z\left(j\right) \ne x)) \Rightarrow ((\forall j \in \operatorname{Fin}\left(r\right),\; (\sum_{s: \operatorname{Fin}\left(n\right)} ((\operatorname{val}\left(s\right) + 1) \cdot z\left(j\right)\left(s\right)) = n)) \Rightarrow ((\forall j \in \operatorname{Fin}\left(r\right),\; (0 < v\left(j\right))) \Rightarrow ((\sum_{j: \operatorname{Fin}\left(r\right)} (v\left(j\right)) = 1) \Rightarrow ((\forall s \in \operatorname{Fin}\left(n\right),\; ((x\left(s\right): \mathbb{R}) = \sum_{j: \operatorname{Fin}\left(r\right)} (v\left(j\right) \cdot (z\left(j\right)\left(s\right): \mathbb{R})))) \Rightarrow (k \le r)))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/ShlykConvexityIndex.shlyk_eventual_convexity_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir A. Shlyk (2026). *On the Vertex Growth Rate of Integer Partition Polytopes and Their Non-Vertex Structure*. URL: <https://arxiv.org/html/2611.24835v1>.

*Commentary.*

Shlyk's 2026 paper formulates eventual existence in Section 1.2 and restates it in Section 3.1. The first sentence of Conjecture 1 in the 2018 preprint gives the strict threshold. An index s in Fin n denotes the positive part size s.val + 1. The lower bound ranges over all finite families of distinct other partitions with arbitrary positive real weights. Repeated summands can be combined by adding their weights.

The construction starts with nonnegative integer equations in paired coordinates. The a-coordinates sum to k and have a common residue modulo k. A nonzero residue forces them all to equal one. In residue zero, exactly one equals k and the others vanish. The paired and congruence equations determine all remaining coordinates. Distinct matrix columns give distinct positive part sizes. A common leading radix digit first bounds the total multiplicity in a putative partition. That bound puts every row sum below the radix, so digit uniqueness recovers the full system without assuming its equations.

Positivity confines each summand to the center's part sizes. On those sizes the integer solutions are the center and the k alternatives. For each a-coordinate, only its own alternative can contribute positively, so all k alternatives are required. Their equal-weight average gives the center. If the encoded center has total m and n exceeds 2m, adjoining the part n minus m preserves the index. Every partition of n has at most one copy of this part. Its center coordinate is one, so every positively weighted summand has one copy, and deleting it recovers a representation of the same cardinality and weights.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/ShlykConvexityIndex.shlyk_eventual_convexity_index`
