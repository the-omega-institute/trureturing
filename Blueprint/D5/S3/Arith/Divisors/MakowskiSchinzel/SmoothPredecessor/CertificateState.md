# Meaning of ordered-table and state checks

## Abstract

Meaning of ordered-table and state checks

**Theorem 1.1 (The order test gives strict order and a lower endpoint).**

$$\forall prev \in \mathbb{N},\; \forall xs \in \operatorname{List}\left(\mathbb{N}\right),\; \operatorname{increasingFrom}\left(prev, xs\right) = true \Leftrightarrow \left(\operatorname{PairwiseLt}\left(xs\right) \land \left(\forall x \in \mathbb{N},\; \operatorname{member}\left(x, xs\right) \Rightarrow prev < x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/CertificateState.increasingFrom_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

A true increasingFrom check means the entries are strictly increasing and every entry exceeds the supplied lower endpoint.

**Theorem 1.2 (A successful first transition exposes its checked state).**

$$\forall ts \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right)\right),\; \forall e \in \mathbb{N},\; \forall es \in \operatorname{List}\left(\mathbb{N}\right),\; \forall st \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \forall end \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \operatorname{stepTable}\left(ts, \operatorname{cons}\left(e, es\right), st\right) = \operatorname{some}\left(end\right) \Leftrightarrow \left(\exists p \in \mathbb{N},\; \exists j \in \mathbb{N},\; \exists L \in \mathbb{N},\; \exists t \in \operatorname{Pair}\left(\mathbb{N}, \operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \operatorname{lookup}\left(oddPrimes, \operatorname{entryLabel}\left(e\right)\right) = \operatorname{some}\left(p\right) \land \left(\operatorname{lookup}\left(st, \operatorname{entryLabel}\left(e\right)\right) = \operatorname{some}\left(\operatorname{pair}\left(j, L\right)\right) \land \left(\operatorname{lookup}\left(ts, \operatorname{entryLabel}\left(e\right)\right) = \operatorname{some}\left(t\right) \land \left(\operatorname{prefixOk}\left(p, j, L, t\right) = true \land \operatorname{stepTable}\left(ts, es, \operatorname{set}\left(st, \operatorname{entryLabel}\left(e\right), \operatorname{pair}\left(j + 1, \operatorname{natDiv}\left(L \cdot \left(\operatorname{entryValue}\left(e\right) - 1\right), \operatorname{entryValue}\left(e\right)\right)\right)\right)\right) = \operatorname{some}\left(end\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/CertificateState.stepTable_head` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

A nonempty successful run identifies a valid label prime p, the current group count j and fixed-point product L, and its tail data t. It checks prefixOk before replacing that state by (j+1,floor(L(q-1)/q)).

**Theorem 1.3 (Chunks compose as optional state transitions).**

$$\forall ts \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right)\right),\; \forall as \in \operatorname{List}\left(\mathbb{N}\right),\; \forall bs \in \operatorname{List}\left(\mathbb{N}\right),\; \forall st \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \operatorname{stepTable}\left(ts, \operatorname{append}\left(as, bs\right), st\right) = \operatorname{bind}\left(\operatorname{stepTable}\left(ts, as, st\right), \operatorname{stepTable}\left(ts, bs\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/CertificateState.stepTable_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

Processing a concatenation first processes the left chunk. A failed transition remains a failure; a successful state starts the right chunk.

**Theorem 1.4 (Terminal group checks are individually available).**

$$\forall ts \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right)\right),\; \forall st \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \operatorname{finalOk}\left(ts, st\right) = true \Leftrightarrow \left(\forall i \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall t \in \operatorname{Pair}\left(\mathbb{N}, \operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \operatorname{lookup}\left(oddPrimes, i\right) = \operatorname{some}\left(p\right) \Rightarrow \left(\operatorname{lookup}\left(st, i\right) = \operatorname{some}\left(\operatorname{pair}\left(j, L\right)\right) \Rightarrow \left(\operatorname{lookup}\left(ts, i\right) = \operatorname{some}\left(t\right) \Rightarrow \operatorname{prefixOk}\left(p, j, L, t\right) = true\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/CertificateState.finalOk_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

The finalOk check is true exactly when prefixOk holds for each index whose prime, state and tail data occur in the three corresponding lists.

**Theorem 1.5 (Ordered concatenation preserves its endpoint).**

$$\forall prev \in \mathbb{N},\; \forall as \in \operatorname{List}\left(\mathbb{N}\right),\; \forall bs \in \operatorname{List}\left(\mathbb{N}\right),\; \operatorname{increasingFrom}\left(prev, \operatorname{append}\left(as, bs\right)\right) = \operatorname{and}\left(\operatorname{increasingFrom}\left(prev, as\right), \operatorname{increasingFrom}\left(\operatorname{getLastD}\left(as, prev\right), bs\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/CertificateState.increasingFrom_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

The second chunk starts after the last value of the first chunk. For an empty first chunk, getLastD retains the original endpoint.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/CertificateState.finalOk_sound`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/CertificateState.increasingFrom_append`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/CertificateState.increasingFrom_sound`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/CertificateState.stepTable_append`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/CertificateState.stepTable_head`
