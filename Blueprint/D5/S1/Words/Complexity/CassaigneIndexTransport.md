# CassaigneIndexTransport

## Abstract

Uniform replication and golden-word asymptotic invariants.

**Theorem 1.1 (hasPeriod block iff).**

$$\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \forall \operatorname{a}: \operatorname{Nat}, \forall \operatorname{L}: \operatorname{Nat}, \forall \operatorname{p}: \operatorname{Nat}, \operatorname{HasPeriod} ((\operatorname{rayPrefix} (\operatorname{index} \mapsto \operatorname{u} (\operatorname{a} + \operatorname{index})) \operatorname{L})) \operatorname{p} \iff 0 < \operatorname{p} \land \forall \operatorname{r} , \operatorname{r} + \operatorname{p} < \operatorname{L} \to \operatorname{u} (\operatorname{a} + \operatorname{r}) = \operatorname{u} (\operatorname{a} + (\operatorname{r} + \operatorname{p}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/CassaigneIndexTransport.hasPeriod_block_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.2 (per is period).**

$$\forall \operatorname{w}: \operatorname{List} \operatorname{Bool}, \operatorname{HasPeriod} \operatorname{w} (\operatorname{per} \operatorname{w})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/CassaigneIndexTransport.per_is_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.3 (per le of period).**

$$\forall \operatorname{w}: \operatorname{List} \operatorname{Bool}, \forall \operatorname{p}: \operatorname{Nat}, (\operatorname{HasPeriod} \operatorname{w} \operatorname{p})\Rightarrow\operatorname{per} \operatorname{w} \leq \operatorname{p}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/CassaigneIndexTransport.per_le_of_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.4 (exponent eq ofReal).**

$$\forall \operatorname{w}: \operatorname{List} \operatorname{Bool}, \operatorname{exponent} \operatorname{w} = \operatorname{ENNReal.ofReal} ((\operatorname{w.length} : \operatorname{Real}) / (\operatorname{per} \operatorname{w} : \operatorname{Real}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/CassaigneIndexTransport.exponent_eq_ofReal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.5 (block exponent le tail).**

$$\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \forall \operatorname{a}: \operatorname{Nat}, \forall \operatorname{m}: \operatorname{Nat}, \forall \operatorname{N}: \operatorname{Nat}, (\operatorname{N} \leq \operatorname{m})\Rightarrow\operatorname{exponent} ((\operatorname{rayPrefix} (\operatorname{index} \mapsto \operatorname{u} (\operatorname{a} + \operatorname{index})) \operatorname{m})) \leq \operatorname{iSup}\left((n:\operatorname{Nat}\mapsto\operatorname{if} \operatorname{N} \leq \operatorname{n} \operatorname{then} \operatorname{indexAt} \operatorname{u} \operatorname{n} \operatorname{else} 0)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/CassaigneIndexTransport.block_exponent_le_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.6 (golden indStar replicated).**

$$\forall \operatorname{k}: \operatorname{Nat}, (0 < \operatorname{k})\Rightarrow\operatorname{indStar} (\operatorname{replicated} \operatorname{k} \operatorname{D5.S1.Words.goldenWord}) = \operatorname{indStar} \operatorname{D5.S1.Words.goldenWord}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/CassaigneIndexTransport.golden_indStar_replicated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

## References

- Truth anchor: `D5/S1/Words/Complexity/CassaigneIndexTransport.block_exponent_le_tail`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneIndexTransport.exponent_eq_ofReal`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneIndexTransport.golden_indStar_replicated`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneIndexTransport.hasPeriod_block_iff`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneIndexTransport.per_is_period`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneIndexTransport.per_le_of_period`
- Dependency: [D5/S0/Computability/Coding/BiasedMassFrontier](../../../S0/Computability/Coding/BiasedMassFrontier.md)
- Dependency: [D5/S1/Words/Complexity/CassaigneRecurrenceTransport](CassaigneRecurrenceTransport.md)
- Dependency: [D5/S1/Words/GoldenWord](../GoldenWord.md)
