# Cyclic mixed-demand coloring

## Abstract

Mixed singleton and double demands on a cyclic distance graph have an exact slot-coloring minimum.

In the formulas, div denotes natural-number division, mod denotes natural remainder, and subtraction on natural numbers is truncated. Angle brackets construct a finite value; proof arguments of cyclicIndex are suppressed under the displayed size inequality.

The packing and slot constructions assume 0<m<=n. Demands are positive and at most two in the mixed minimum; the general slot theorem allows larger finite demands.

**Definition 1.1 (Demand types).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall k: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{N}\right)\right), \left(\operatorname{Vertex}\left(k\right) = \Sigma_{t:\operatorname{Fin}\left(n\right)} \operatorname{Fin}\left(\operatorname{k}\left(t\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There are n cyclic prefixes. Prefix t has k(t) types, indexed by Fin(k(t)). A vertex is a prefix together with a type rank. Rank zero is used for every singleton, independently of any external label attached to that singleton.

**Definition 1.2 (Integer circular adjacency).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall i: \left(\operatorname{Fin}\left(n\right)\right), \left(\forall j: \left(\operatorname{Fin}\left(n\right)\right), \left(\left(\operatorname{Near}\left(m, i, j\right)\right) \iff \left(\left(\left(\operatorname{val}\left(i\right) < \left(\operatorname{val}\left(j\right)\right) + \left(m\right)\right) \land \left(\operatorname{val}\left(j\right) < \left(\operatorname{val}\left(i\right)\right) + \left(m\right)\right)\right) \lor \left(\left(\left(n\right) + \left(\operatorname{val}\left(i\right)\right) < \left(\operatorname{val}\left(j\right)\right) + \left(m\right)\right) \lor \left(\left(n\right) + \left(\operatorname{val}\left(j\right)\right) < \left(\operatorname{val}\left(i\right)\right) + \left(m\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.Near` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two prefixes are near when their integer circular distance is strictly less than m. The definition includes the ordinary interval and both orientations across the seam. For positive m a prefix is near itself.

**Definition 1.3 (Proper demand coloring).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall Z: \left(Type\right), \left(\forall k: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{N}\right)\right), \left(\forall color: \left(\left(\operatorname{Vertex}\left(k\right)\right) \to \left(Z\right)\right), \left(\left(\operatorname{Proper}\left(m, k, color\right)\right) \iff \left(\forall x: \left(\operatorname{Vertex}\left(k\right)\right), \left(\forall y: \left(\operatorname{Vertex}\left(k\right)\right), \left(\left(\left(x \neq y\right) \land \left(\operatorname{Near}\left(m, \operatorname{fst}\left(x\right), \operatorname{fst}\left(y\right)\right)\right)\right) \implies \left(\operatorname{color}\left(x\right) \neq \operatorname{color}\left(y\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.Proper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A coloring separates every pair of distinct types whose prefixes are near. For m>0, all types at a single prefix have different colors.

**Theorem 1.4 (Cyclic packing).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall k: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{N}\right)\right), \left(\forall S: \left(\operatorname{Finset}\left(\operatorname{Vertex}\left(k\right)\right)\right), \left(\left(\left(\left(0 < m\right) \land \left(m \le n\right)\right) \land \left(\forall x: \left(\operatorname{Vertex}\left(k\right)\right), \left(\forall y: \left(\operatorname{Vertex}\left(k\right)\right), \left(\left(\left(x \in S\right) \land \left(\left(y \in S\right) \land \left(x \neq y\right)\right)\right) \implies \left(\neg\left(\operatorname{Near}\left(m, \operatorname{fst}\left(x\right), \operatorname{fst}\left(y\right)\right)\right)\right)\right)\right)\right)\right) \implies \left(\operatorname{card}\left(S\right) \le \operatorname{div}\left(n, m\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.separated_packing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<m<=n, every finite set of pairwise separated types has cardinality at most floor(n/m). Attach the next m cyclic positions to each selected type. These intervals are disjoint: an intersection forces near prefixes, and different types at one prefix are also forbidden. Their injection into the n positions gives m times the cardinality at most n. The argument includes empty sets, singleton sets, and intervals crossing the seam.

**Theorem 1.5 (Total demand bound).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall c: \left(\mathbb{N}\right), \left(\forall k: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{N}\right)\right), \left(\forall color: \left(\left(\operatorname{Vertex}\left(k\right)\right) \to \left(\operatorname{Fin}\left(c\right)\right)\right), \left(\left(\left(\left(0 < m\right) \land \left(m \le n\right)\right) \land \left(\operatorname{Proper}\left(m, k, color\right)\right)\right) \implies \left(\operatorname{sum}\left(\operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right), k\right) \le \left(c\right) \cdot \left(\operatorname{div}\left(n, m\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.packing_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<m<=n, every proper coloring with c colors satisfies sum(k)<=c floor(n/m). Partition the types by color and apply the cyclic packing bound to every color class.

**Definition 1.6 (Wrapping block sums).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall i: \left(\mathbb{N}\right), \left(\forall s: \left(\left(\mathbb{N}\right) \to \left(\mathbb{N}\right)\right), \left(\operatorname{Window}\left(n, m, s, i\right) = if \left(i\right) + \left(m\right) \le n then \left(\operatorname{s}\left(\left(i\right) + \left(m\right)\right)\right) - \left(\operatorname{s}\left(i\right)\right) else \left(\left(\left(\operatorname{s}\left(n\right)\right) - \left(\operatorname{s}\left(i\right)\right)\right) + \left(\operatorname{s}\left(\left(\left(i\right) + \left(m\right)\right) - \left(n\right)\right)\right)\right) - \left(\operatorname{s}\left(0\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.Window` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A cumulative boundary function s represents the slot blocks. A nonwrapping m-block sum is s(i+m)-s(i). A wrapping sum is s(n)-s(i)+s(i+m-n)-s(0).

**Theorem 1.7 (Cyclic slot validity).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall c: \left(\mathbb{N}\right), \left(\forall k: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{N}\right)\right), \left(\forall s: \left(\left(\mathbb{N}\right) \to \left(\mathbb{N}\right)\right), \left(\left(\left(\left(0 < m\right) \land \left(m \le n\right)\right) \land \left(\left(0 < c\right) \land \left(\left(\operatorname{s}\left(0\right) = 0\right) \land \left(\left(\forall i: \left(\mathbb{N}\right), \left(\left(i < n\right) \implies \left(\operatorname{s}\left(i\right) < \operatorname{s}\left(\left(i\right) + \left(1\right)\right)\right)\right)\right) \land \left(\left(\forall t: \left(\operatorname{Fin}\left(n\right)\right), \left(\operatorname{k}\left(t\right) \le \left(\operatorname{s}\left(\left(\operatorname{val}\left(t\right)\right) + \left(1\right)\right)\right) - \left(\operatorname{s}\left(\operatorname{val}\left(t\right)\right)\right)\right)\right) \land \left(\left(\operatorname{mod}\left(\operatorname{s}\left(n\right), c\right) = 0\right) \land \left(\forall i: \left(\mathbb{N}\right), \left(\left(i < n\right) \implies \left(\operatorname{Window}\left(n, m, s, i\right) \le c\right)\right)\right)\right)\right)\right)\right)\right)\right) \implies \left(\operatorname{Proper}\left(m, k, \lambda x: \left(\operatorname{Vertex}\left(k\right)\right) \mapsto \left(\langle\operatorname{mod}\left(\left(\operatorname{s}\left(\operatorname{val}\left(\operatorname{fst}\left(x\right)\right)\right)\right) + \left(\operatorname{val}\left(\operatorname{snd}\left(x\right)\right)\right), c\right)\rangle:\operatorname{Fin}\left(c\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.cyclic_slot_coloring` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume 0<m<=n, c>0, s(0)=0, strictly positive blocks s(i+1)-s(i), k(i)<=s(i+1)-s(i), c divides s(n), and every wrapping m-block sum is at most c. Color rank r at prefix i by (s(i)+r) mod c. For an adjacent ordered pair, selected slots are strictly ordered and less than c apart. Across the seam translate the second slot by s(n), which preserves its residue. Distinct ranks in one block are handled by the same strict bound. Thus the coloring is proper, including equality of a window sum with c.

**Theorem 1.8 (Exact shortened-slot formula).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall a: \left(\mathbb{N}\right), \left(\forall rho: \left(\mathbb{N}\right), \left(\forall k: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{N}\right)\right), \left(\forall R: \left(\operatorname{Finset}\left(\mathbb{N}\right)\right), \left(\left(\left(\left(0 < m\right) \land \left(m \le n\right)\right) \land \left(\left(n = \left(\left(m\right) \cdot \left(a\right)\right) + \left(rho\right)\right) \land \left(\left(\forall t: \left(\operatorname{Fin}\left(n\right)\right), \left(\left(\operatorname{k}\left(t\right) = 1\right) \lor \left(\operatorname{k}\left(t\right) = 2\right)\right)\right) \land \left(\left(R \subseteq \operatorname{range}\left(n\right)\right) \land \left(\left(\operatorname{card}\left(R\right) = \left(2\right) \cdot \left(rho\right)\right) \land \left(\forall t: \left(\operatorname{Fin}\left(n\right)\right), \left(\left(\operatorname{val}\left(t\right) \in R\right) \implies \left(\operatorname{k}\left(t\right) = 1\right)\right)\right)\right)\right)\right)\right)\right) \implies \left(let s: \left(\mathbb{N}\right) \to \left(\mathbb{N}\right) := \lambda i: \left(\mathbb{N}\right) \mapsto \left(\left(\left(2\right) \cdot \left(i\right)\right) - \left(\operatorname{card}\left(\operatorname{filter}\left(R, \lambda t: \left(\mathbb{N}\right) \mapsto \left(t < i\right)\right)\right)\right)\right); \left(\left(\operatorname{s}\left(0\right) = 0\right) \land \left(\left(\forall i: \left(\mathbb{N}\right), \left(\left(\operatorname{s}\left(\left(i\right) + \left(1\right)\right)\right) - \left(\operatorname{s}\left(i\right)\right) = if i \in R then 1 else 2\right)\right) \land \left(\left(\operatorname{s}\left(n\right) = \left(\left(2\right) \cdot \left(m\right)\right) \cdot \left(a\right)\right) \land \left(\operatorname{Proper}\left(m, k, \lambda x: \left(\operatorname{Vertex}\left(k\right)\right) \mapsto \left(\langle\operatorname{mod}\left(\left(\operatorname{s}\left(\operatorname{val}\left(\operatorname{fst}\left(x\right)\right)\right)\right) + \left(\operatorname{val}\left(\operatorname{snd}\left(x\right)\right)\right), \left(2\right) \cdot \left(m\right)\right)\rangle:\operatorname{Fin}\left(\left(2\right) \cdot \left(m\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.low_slot_formula_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the shortened singleton blocks, the displayed cumulative formula starts at zero, has length one exactly on R and length two elsewhere, ends at 2ma, and its chosen slot residues form a proper coloring. The existential constructor uses this coloring.

**Theorem 1.9 (Shortened singleton blocks).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall a: \left(\mathbb{N}\right), \left(\forall rho: \left(\mathbb{N}\right), \left(\forall k: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{N}\right)\right), \left(\forall R: \left(\operatorname{Finset}\left(\mathbb{N}\right)\right), \left(\left(\left(\left(0 < m\right) \land \left(m \le n\right)\right) \land \left(\left(n = \left(\left(m\right) \cdot \left(a\right)\right) + \left(rho\right)\right) \land \left(\left(\forall t: \left(\operatorname{Fin}\left(n\right)\right), \left(\left(\operatorname{k}\left(t\right) = 1\right) \lor \left(\operatorname{k}\left(t\right) = 2\right)\right)\right) \land \left(\left(R \subseteq \operatorname{range}\left(n\right)\right) \land \left(\left(\operatorname{card}\left(R\right) = \left(2\right) \cdot \left(rho\right)\right) \land \left(\forall t: \left(\operatorname{Fin}\left(n\right)\right), \left(\left(\operatorname{val}\left(t\right) \in R\right) \implies \left(\operatorname{k}\left(t\right) = 1\right)\right)\right)\right)\right)\right)\right)\right) \implies \left(\exists color: \left(\left(\operatorname{Vertex}\left(k\right)\right) \to \left(\operatorname{Fin}\left(\left(2\right) \cdot \left(m\right)\right)\right)\right), \left(\operatorname{Proper}\left(m, k, color\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.low_slot_construction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume 0<m<=n, n=ma+rho, and every demand is one or two. Choose a set R of exactly 2rho singleton prefixes. Set s(i)=2i-#{r in R:r<i}. Each chosen block has length one; every other block has length two. All demands are contained, the total is 2ma, and every wrapping m-block sum is at most 2m. Cyclic slot validity supplies 2m colors for any placement of the chosen singleton prefixes.

**Theorem 1.10 (The low branch).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall a: \left(\mathbb{N}\right), \left(\forall rho: \left(\mathbb{N}\right), \left(\forall k: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{N}\right)\right), \left(\left(\left(\left(0 < m\right) \land \left(m \le n\right)\right) \land \left(\left(n = \left(\left(m\right) \cdot \left(a\right)\right) + \left(rho\right)\right) \land \left(\left(\forall t: \left(\operatorname{Fin}\left(n\right)\right), \left(\left(\operatorname{k}\left(t\right) = 1\right) \lor \left(\operatorname{k}\left(t\right) = 2\right)\right)\right) \land \left(\left(2\right) \cdot \left(rho\right) \le \operatorname{card}\left(\operatorname{filter}\left(\operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right), \lambda t: \left(\operatorname{Fin}\left(n\right)\right) \mapsto \left(\operatorname{k}\left(t\right) = 1\right)\right)\right)\right)\right)\right)\right) \implies \left(\exists color: \left(\left(\operatorname{Vertex}\left(k\right)\right) \to \left(\operatorname{Fin}\left(\left(2\right) \cdot \left(m\right)\right)\right)\right), \left(\operatorname{Proper}\left(m, k, color\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.low_branch_coloring` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume 0<m<=n, n=ma+rho, and every demand is one or two. If there are at least 2rho singleton prefixes, select exactly 2rho of them and use the shortened-block construction. No contiguous placement condition is imposed on the singletons.

**Theorem 1.11 (Spaced extra slots).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall k: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{N}\right)\right), \left(\forall R: \left(\operatorname{Finset}\left(\mathbb{N}\right)\right), \left(\left(\left(\left(0 < m\right) \land \left(m \le n\right)\right) \land \left(\left(\forall t: \left(\operatorname{Fin}\left(n\right)\right), \left(\operatorname{k}\left(t\right) \le 2\right)\right) \land \left(\left(R \subseteq \operatorname{range}\left(n\right)\right) \land \left(\left(\forall x: \left(\mathbb{N}\right), \left(\forall y: \left(\mathbb{N}\right), \left(\left(\left(x \in R\right) \land \left(\left(y \in R\right) \land \left(x \neq y\right)\right)\right) \implies \left(\neg\left(\left(\left(x < \left(y\right) + \left(m\right)\right) \land \left(y < \left(x\right) + \left(m\right)\right)\right) \lor \left(\left(\left(n\right) + \left(x\right) < \left(y\right) + \left(m\right)\right) \lor \left(\left(n\right) + \left(y\right) < \left(x\right) + \left(m\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\operatorname{mod}\left(\left(\left(2\right) \cdot \left(n\right)\right) + \left(\operatorname{card}\left(R\right)\right), \left(\left(2\right) \cdot \left(m\right)\right) + \left(1\right)\right) = 0\right)\right)\right)\right)\right) \implies \left(\exists color: \left(\left(\operatorname{Vertex}\left(k\right)\right) \to \left(\operatorname{Fin}\left(\left(\left(2\right) \cdot \left(m\right)\right) + \left(1\right)\right)\right)\right), \left(\operatorname{Proper}\left(m, k, color\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.spaced_slot_construction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume 0<m<=n and every demand is at most two. Start with blocks of length two and add one slot at each prefix in a cyclically m-separated set R. Set s(i)=2i+#{r in R:r<i}. Every wrapping m-window contains at most one extra slot, so its sum is at most 2m+1. If 2m+1 divides 2n+|R|, this gives a proper coloring with 2m+1 colors.

**Theorem 1.12 (Exact spaced-slot formula).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall a: \left(\mathbb{N}\right), \left(\forall rho: \left(\mathbb{N}\right), \left(\forall k: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{N}\right)\right), \left(\left(\left(\left(0 < m\right) \land \left(m \le n\right)\right) \land \left(\left(n = \left(\left(m\right) \cdot \left(a\right)\right) + \left(rho\right)\right) \land \left(\left(\left(2\right) \cdot \left(rho\right) \le a\right) \land \left(\forall t: \left(\operatorname{Fin}\left(n\right)\right), \left(\operatorname{k}\left(t\right) \le 2\right)\right)\right)\right)\right) \implies \left(let c: \mathbb{N} := \left(\left(2\right) \cdot \left(m\right)\right) + \left(1\right); \left(let z: \mathbb{N} := \operatorname{mod}\left(\left(a\right) - \left(\left(2\right) \cdot \left(rho\right)\right), c\right); \left(let R: \operatorname{Finset}\left(\mathbb{N}\right) := \operatorname{image}\left(\operatorname{range}\left(z\right), \lambda q: \left(\mathbb{N}\right) \mapsto \left(\left(q\right) \cdot \left(m\right)\right)\right); \left(let s: \left(\mathbb{N}\right) \to \left(\mathbb{N}\right) := \lambda i: \left(\mathbb{N}\right) \mapsto \left(\left(\left(2\right) \cdot \left(i\right)\right) + \left(\operatorname{card}\left(\operatorname{filter}\left(R, \lambda t: \left(\mathbb{N}\right) \mapsto \left(t < i\right)\right)\right)\right)\right); \left(\left(\operatorname{s}\left(0\right) = 0\right) \land \left(\left(\operatorname{s}\left(n\right) = \left(\left(2\right) \cdot \left(n\right)\right) + \left(z\right)\right) \land \left(\operatorname{Proper}\left(m, k, \lambda x: \left(\operatorname{Vertex}\left(k\right)\right) \mapsto \left(\langle\operatorname{mod}\left(\left(\operatorname{s}\left(\operatorname{val}\left(\operatorname{fst}\left(x\right)\right)\right)\right) + \left(\operatorname{val}\left(\operatorname{snd}\left(x\right)\right)\right), c\right)\rangle:\operatorname{Fin}\left(c\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.high_slot_formula_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With c=2m+1, z=(a-2rho) mod c, and R={qm:0<=q<z}, the cumulative formula starts at zero, ends at 2n+z, and its chosen slot residues form a proper coloring. The high-branch constructor uses this coloring.

**Theorem 1.13 (The high branch).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall a: \left(\mathbb{N}\right), \left(\forall rho: \left(\mathbb{N}\right), \left(\forall k: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{N}\right)\right), \left(\left(\left(\left(0 < m\right) \land \left(m \le n\right)\right) \land \left(\left(n = \left(\left(m\right) \cdot \left(a\right)\right) + \left(rho\right)\right) \land \left(\left(\left(2\right) \cdot \left(rho\right) \le a\right) \land \left(\forall t: \left(\operatorname{Fin}\left(n\right)\right), \left(\operatorname{k}\left(t\right) \le 2\right)\right)\right)\right)\right) \implies \left(\exists color: \left(\left(\operatorname{Vertex}\left(k\right)\right) \to \left(\operatorname{Fin}\left(\left(\left(2\right) \cdot \left(m\right)\right) + \left(1\right)\right)\right)\right), \left(\operatorname{Proper}\left(m, k, color\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.high_branch_coloring` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume 0<m<=n, n=ma+rho, a>=2rho, and every demand is at most two. Put c=2m+1 and z=(a-2rho) mod c. Add slots at 0,m,...,(z-1)m. Since z<=a, consecutive extras and the cyclic closing gap are at least m apart. The identity 2n+(a-2rho)=ca shows that c divides 2n+z. This construction allows arbitrary singleton positions and even applies when every demand is two.

**Definition 1.14 (A cyclic consecutive window).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\left(m \le n\right) \implies \left(\forall start: \left(\operatorname{Fin}\left(n\right)\right), \left(\forall i: \left(\operatorname{Fin}\left(m\right)\right), \left(\operatorname{val}\left(\operatorname{cyclicIndex}\left(start, i\right)\right) = if \left(\operatorname{val}\left(start\right)\right) + \left(\operatorname{val}\left(i\right)\right) < n then \left(\operatorname{val}\left(start\right)\right) + \left(\operatorname{val}\left(i\right)\right) else \left(\left(\operatorname{val}\left(start\right)\right) + \left(\operatorname{val}\left(i\right)\right)\right) - \left(n\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.cyclicIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The offset i from start is start+i when this is below n, and start+i-n otherwise. Offsets range over Fin(m), with m<=n, so there is at most one seam crossing.

**Theorem 1.15 (The double-demand clique).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall c: \left(\mathbb{N}\right), \left(\forall k: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{N}\right)\right), \left(\forall start: \left(\operatorname{Fin}\left(n\right)\right), \left(\forall color: \left(\left(\operatorname{Vertex}\left(k\right)\right) \to \left(\operatorname{Fin}\left(c\right)\right)\right), \left(\left(\left(m \le n\right) \land \left(\left(\forall i: \left(\operatorname{Fin}\left(m\right)\right), \left(\operatorname{k}\left(\operatorname{cyclicIndex}\left(start, i\right)\right) = 2\right)\right) \land \left(\operatorname{Proper}\left(m, k, color\right)\right)\right)\right) \implies \left(\left(2\right) \cdot \left(m\right) \le c\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.double_window_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an m-consecutive cyclic window consists entirely of double-demand prefixes, its 2m types form a clique. Their colors are distinct, giving c>=2m for every proper coloring.

**Theorem 1.16 (The exact mixed minimum).**

$$\forall n: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall a: \left(\mathbb{N}\right), \left(\forall rho: \left(\mathbb{N}\right), \left(\forall k: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{N}\right)\right), \left(\forall start: \left(\operatorname{Fin}\left(n\right)\right), \left(\left(\left(2 \le m\right) \land \left(\left(\left(2\right) \cdot \left(m\right) < n\right) \land \left(\left(n = \left(\left(m\right) \cdot \left(a\right)\right) + \left(rho\right)\right) \land \left(\left(rho < m\right) \land \left(\left(\left(2\right) \cdot \left(rho\right) \le a\right) \land \left(\left(\forall t: \left(\operatorname{Fin}\left(n\right)\right), \left(\left(\operatorname{k}\left(t\right) = 1\right) \lor \left(\operatorname{k}\left(t\right) = 2\right)\right)\right) \land \left(\forall i: \left(\operatorname{Fin}\left(m\right)\right), \left(\operatorname{k}\left(\operatorname{cyclicIndex}\left(start, i\right)\right) = 2\right)\right)\right)\right)\right)\right)\right)\right) \implies \left(let L: \mathbb{N} := \operatorname{card}\left(\operatorname{filter}\left(\operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right), \lambda t: \left(\operatorname{Fin}\left(n\right)\right) \mapsto \left(\operatorname{k}\left(t\right) = 1\right)\right)\right); \left(let capacity: \mathbb{N} := \operatorname{max}\left(\left(2\right) \cdot \left(m\right), \operatorname{div}\left(\left(\left(\left(\left(2\right) \cdot \left(n\right)\right) - \left(L\right)\right) + \left(a\right)\right) - \left(1\right), a\right)\right); \left(\left(\operatorname{IsLeast}\left(\{c: \mathbb{N} \mid \exists color: \left(\left(\operatorname{Vertex}\left(k\right)\right) \to \left(\operatorname{Fin}\left(c\right)\right)\right), \left(\operatorname{Proper}\left(m, k, color\right)\right)\}, capacity\right)\right) \land \left(capacity = \left(\left(2\right) \cdot \left(m\right)\right) + \left(if L < \left(2\right) \cdot \left(rho\right) then 1 else 0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.mixed_demand_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume m>=2, n>2m, n=ma+rho, rho<m, a>=2rho, demands k(t) in {1,2}, and one m-consecutive all-double window. Let L be the number of singleton prefixes. The least feasible number of colors is max(2m,ceil((2n-L)/a)), exactly 2m+1 when L<2rho and 2m otherwise. Natural ceiling is represented by (2n-L+a-1)/a; the hypotheses imply a>0. The clique gives the 2m lower bound, packing uses floor(n/m)=a and total demand 2n-L, and the two slot constructions attain the stated bound. This is a theorem about cyclic demand types; additional physical observation data require their own correspondence.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.Near`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.Proper`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.Window`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.cyclicIndex`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.cyclic_slot_coloring`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.double_window_lower_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.high_branch_coloring`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.high_slot_formula_valid`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.low_branch_coloring`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.low_slot_construction`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.low_slot_formula_valid`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.mixed_demand_minimum`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.packing_lower_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.separated_packing`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.spaced_slot_construction`
