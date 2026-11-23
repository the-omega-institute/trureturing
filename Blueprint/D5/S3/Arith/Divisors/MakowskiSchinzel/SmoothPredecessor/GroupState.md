# Every prefix of a labelled group

## Abstract

Every prefix of a labelled group

**Theorem 1.1 (Projection of a successful table run).**

$$\forall ts \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right)\right),\; \forall es \in \operatorname{List}\left(\mathbb{N}\right),\; \forall st \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \forall end \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \forall i \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall t \in \operatorname{Pair}\left(\mathbb{N}, \operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \operatorname{stepTable}\left(ts, es, st\right) = \operatorname{some}\left(end\right) \Rightarrow \left(\operatorname{lookup}\left(oddPrimes, i\right) = \operatorname{some}\left(p\right) \Rightarrow \left(\operatorname{lookup}\left(st, i\right) = \operatorname{some}\left(\operatorname{pair}\left(j, L\right)\right) \Rightarrow \left(\operatorname{lookup}\left(ts, i\right) = \operatorname{some}\left(t\right) \Rightarrow \left(\operatorname{lookup}\left(end, i\right) = \operatorname{some}\left(\operatorname{pair}\left(j + \operatorname{length}\left(\operatorname{groupValues}\left(i, es\right)\right), \operatorname{fixedProduct}\left(L, \operatorname{groupValues}\left(i, es\right)\right)\right)\right) \land \left(\forall k \in \mathbb{N},\; k < \operatorname{length}\left(\operatorname{groupValues}\left(i, es\right)\right) \Rightarrow \operatorname{prefixOk}\left(p, j + k, \operatorname{fixedProduct}\left(L, \operatorname{take}\left(k, \operatorname{groupValues}\left(i, es\right)\right)\right), t\right) = true\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/GroupState.stepTable_group` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

Fix a group index i and an initial state (j,L). Filtering a successful table run by that label preserves its order, increments the count by the number of matching entries, and replaces L by the successive integer quotients floor(L(q-1)/q). Every proper prefix passes prefixOk.

**Theorem 1.2 (Integer products bound rational products from below).**

$$\forall L \in \mathbb{N},\; \forall qs \in \operatorname{List}\left(\mathbb{N}\right),\; \operatorname{fixedProduct}\left(L, qs\right) \le L \cdot \operatorname{lowerProduct}\left(qs\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/GroupState.fixedProduct_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

For every finite list of natural numbers q, including zero, rounding down after each multiplication gives at most L times the exact rational product of (q-1)/q. The lowerProduct notation denotes precisely that product.

**Theorem 1.3 (Terminal checks include the last prefix).**

$$\forall ts \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right)\right),\; \forall es \in \operatorname{List}\left(\mathbb{N}\right),\; \forall st \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \forall end \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \forall i \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall t \in \operatorname{Pair}\left(\mathbb{N}, \operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \operatorname{stepTable}\left(ts, es, st\right) = \operatorname{some}\left(end\right) \Rightarrow \left(\operatorname{lookup}\left(oddPrimes, i\right) = \operatorname{some}\left(p\right) \Rightarrow \left(\operatorname{lookup}\left(st, i\right) = \operatorname{some}\left(\operatorname{pair}\left(j, L\right)\right) \Rightarrow \left(\operatorname{lookup}\left(ts, i\right) = \operatorname{some}\left(t\right) \Rightarrow \left(\left(\forall k \in \mathbb{N},\; k \le \operatorname{length}\left(\operatorname{groupValues}\left(i, es\right)\right) \Rightarrow \operatorname{prefixOk}\left(p, j + k, \operatorname{fixedProduct}\left(L, \operatorname{take}\left(k, \operatorname{groupValues}\left(i, es\right)\right)\right), t\right) = true\right) \Leftrightarrow \operatorname{prefixOk}\left(p, j + \operatorname{length}\left(\operatorname{groupValues}\left(i, es\right)\right), \operatorname{fixedProduct}\left(L, \operatorname{groupValues}\left(i, es\right)\right), t\right) = true\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/GroupState.stepTable_all_prefixes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

Under a successful run, every prefix passes exactly when its last prefix passes. All proper prefixes occur before a transition; no other group is required.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/GroupState.fixedProduct_le`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/GroupState.stepTable_all_prefixes`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/GroupState.stepTable_group`
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/CertificateState](CertificateState.md)
