# Full-set sequencing in finite abelian groups

## Abstract

Gordon sequencing preserves every original label and coefficient one.

**Theorem 1.1 (The total and the unique involution).**

$$\forall G \in Type*,\; [\operatorname{AddCommGroup}\left(G\right)] [\operatorname{Fintype}\left(G\right)] (\operatorname{total}\left(G\right) \ne 0) \Leftrightarrow (\exists t \in G,\; ((t \ne 0) \land (t+t = 0)) \land (\forall x \in G,\; ((x \ne 0) \land (x+x = 0)) \Rightarrow (x = t)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GordonFullSet.sum_ne_zero_iff_unique_involution` (`✓ std3`). ∎

*Citation.* Basil Gordon (1961). *Sequences in groups with distinct partial products*. DOI: [10.2140/pjm.1961.11.1309](https://doi.org/10.2140/pjm.1961.11.1309). URL: <https://msp.org/pjm/1961/11-4/p14.xhtml>.

*Commentary.*

Nonzero total gives one positive even prime-power factor and an odd digit box. Its unique nonzero element killed by doubling is the terminal prefix (h,0); the box has injective doubling. Conversely, after removing the unique nonzero involution, negation pairs every remaining nonzero term with its negative. The total therefore equals that involution. The sequencing theorem consumes this equivalence before selecting its prime-power presentation.

**Theorem 1.2 (The complete finite-abelian theorem).**

$$\forall G \in Type*,\; [\operatorname{AddCommGroup}\left(G\right)] [\operatorname{Fintype}\left(G\right)] (\operatorname{total}\left(G\right) \ne 0) \Rightarrow (\exists w \in \operatorname{List}\left(G\right),\; ((\operatorname{Nodup}\left(w\right)) \land (\forall x \in G,\; (x \in w) \Leftrightarrow (x \ne 0))) \land ((\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; ((k \le \operatorname{length}\left(w\right)) \land (l \le \operatorname{length}\left(w\right))) \Rightarrow ((\operatorname{sum}\left(\operatorname{take}\left(k, w\right)\right) = \operatorname{sum}\left(\operatorname{take}\left(l, w\right)\right)) \Rightarrow (k = l))) \land (\forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; ((i < j) \land (j \le \operatorname{length}\left(w\right))) \Rightarrow (\operatorname{sum}\left(\operatorname{take}\left(j-i, \operatorname{drop}\left(i, w\right)\right)\right) \ne 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GordonFullSet.exists_full_set_sequencing` (`✓ std3`). ∎

*Citation.* Basil Gordon (1961). *Sequences in groups with distinct partial products*. DOI: [10.2140/pjm.1961.11.1309](https://doi.org/10.2140/pjm.1961.11.1309). URL: <https://msp.org/pjm/1961/11-4/p14.xhtml>.

*Commentary.*

Total means the sum of all elements of the finite additive abelian group. A nonzero total forces exactly one nontrivial even prime-power factor in the finite-abelian decomposition. Odd factors have zero total because doubling is invertible; two even factors make every coordinate total vanish by the product cardinality multiplicities. Trivial exponents are removed and the remaining odd prime powers form the digit box. The inverse additive equivalence transports the complete product word to the original group. Each original nonzero element occurs exactly once with coefficient one. Every prefix, including zero and the whole word, is distinct; subtraction of two prefixes gives the nonzero sum of every nonempty interval. This is Gordon's published full-set result. The arbitrary-subset problem remains unresolved by this construction, since deleting labels changes prefix sums.

## References

- Truth anchor: `D5/S3/FiniteGroups/GordonFullSet.exists_full_set_sequencing`
- Truth anchor: `D5/S3/FiniteGroups/GordonFullSet.sum_ne_zero_iff_unique_involution`
- Dependency: [D5/S3/FiniteGroups/GordonProduct](GordonProduct.md)
