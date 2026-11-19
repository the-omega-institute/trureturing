# CassaigneRecurrenceTransport

## Abstract

Uniform replication and golden-word asymptotic invariants.

**Definition 1.1 (factorLanguage).**

$$\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \forall \operatorname{n}: \operatorname{Nat}, \operatorname{factorLanguage} \operatorname{u} \operatorname{n} = \{ \operatorname{w} \mid \exists \operatorname{i}: \operatorname{Nat}, \operatorname{w} = \operatorname{List.ofFn} (\operatorname{j}: \operatorname{Fin} \operatorname{n} \mapsto \operatorname{u} (\operatorname{i} + \operatorname{j.1})) \}$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.factorLanguage` (`✓ std3`).

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

Printed p. 701: “Lₙ(u) denotes the language of factors of length n of u (i.e., finite words of length n that occur as a block of consecutive letters of u) and L(u) the language of all factors of u.” Lists represent finite words; the starting index is natural.

**Definition 1.2 (HasPeriod).**

$$\forall \operatorname{w}: \operatorname{List} \operatorname{Bool}, \forall \operatorname{p}: \operatorname{Nat}, \operatorname{HasPeriod} \operatorname{w} \operatorname{p} = (0 < \operatorname{p} \land \forall \operatorname{i}: \operatorname{Nat}, \operatorname{i} + \operatorname{p} < \operatorname{w.length} \to \operatorname{w.getD} \operatorname{i} \operatorname{false} = \operatorname{w.getD} (\operatorname{i} + \operatorname{p}) \operatorname{false})$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.HasPeriod` (`✓ std3`).

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

The displayed definition uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Definition 1.3 (per).**

$$\forall \operatorname{w}: \operatorname{List} \operatorname{Bool}, \operatorname{per} \operatorname{w} = (\operatorname{sInf} \{ \operatorname{p} : \operatorname{Nat} \mid \operatorname{HasPeriod} \operatorname{w} \operatorname{p} \})$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.per` (`✓ std3`).

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

The displayed definition uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Definition 1.4 (exponent).**

$$\forall \operatorname{w}: \operatorname{List} \operatorname{Bool}, \operatorname{exponent} \operatorname{w} = ((\operatorname{w.length} : \operatorname{ENNReal}) / (\operatorname{per} \operatorname{w} : \operatorname{ENNReal}))$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.exponent` (`✓ std3`).

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

Printed p. 702, Section 2.1: “The exponent e(w) of a word w ∈ A* is the maximum of |w|/|z| over all words z ∈ A+ such that w is a prefix of zω.” Thus its value is the word length divided by its least positive period.

**Definition 1.5 (indexAt).**

$$\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \forall \operatorname{n}: \operatorname{Nat}, \operatorname{indexAt} \operatorname{u} \operatorname{n} = (\operatorname{iSup}\left((w:\{ \operatorname{w} : \operatorname{List} \operatorname{Bool} / / \operatorname{w} \in \operatorname{factorLanguage} \operatorname{u} \operatorname{n} \}\mapsto\operatorname{exponent} \operatorname{w.1})\right))$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.indexAt` (`✓ std3`).

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

The displayed definition uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Definition 1.6 (indStar).**

$$\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \operatorname{indStar} \operatorname{u} = (\operatorname{iInf}\left((N:\operatorname{Nat}\mapsto\operatorname{iSup}\left((n:\operatorname{Nat}\mapsto\operatorname{if} \operatorname{N} \leq \operatorname{n} \operatorname{then} \operatorname{indexAt} \operatorname{u} \operatorname{n} \operatorname{else} 0)\right))\right))$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.indStar` (`✓ std3`).

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

Printed pp. 703–704, Section 2.2: “ind*(u) = lim supₙ→∞ {e(w) : w ∈ L(u) and |w| ≥ n} ∈ [1, +∞].” The complete lattice ENNReal supplies the infimum of the tail suprema.

**Definition 1.7 (HasRecurrenceBound).**

$$\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \forall \operatorname{n}: \operatorname{Nat}, \forall \operatorname{N}: \operatorname{Nat}, \operatorname{HasRecurrenceBound} \operatorname{u} \operatorname{n} \operatorname{N} = (\forall \operatorname{w}: \operatorname{List} \operatorname{Bool}, \operatorname{w} \in \operatorname{factorLanguage} \operatorname{u} \operatorname{N} \to \forall \operatorname{x}: \operatorname{List} \operatorname{Bool}, \operatorname{x} \in \operatorname{factorLanguage} \operatorname{u} \operatorname{n} \to \exists \operatorname{i}: \operatorname{Nat}, \operatorname{i} + \operatorname{x.length} \leq \operatorname{w.length} \land \forall \operatorname{j}: \operatorname{Fin} \operatorname{x.length}, \operatorname{x.getD} \operatorname{j.1} \operatorname{false} = \operatorname{w.getD} (\operatorname{i} + \operatorname{j.1}) \operatorname{false})$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.HasRecurrenceBound` (`✓ std3`).

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

The displayed definition uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Definition 1.8 (recurrenceCandidates).**

$$\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \forall \operatorname{n}: \operatorname{Nat}, \operatorname{recurrenceCandidates} \operatorname{u} \operatorname{n} = (\{ \operatorname{r} \mid \exists \operatorname{N} : \operatorname{Nat} , \operatorname{r} = (\operatorname{N} : \operatorname{ENat}) \land \operatorname{HasRecurrenceBound} \operatorname{u} \operatorname{n} \operatorname{N} \})$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.recurrenceCandidates` (`✓ std3`).

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

The displayed definition uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Definition 1.9 (recurrenceFunction).**

$$\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \forall \operatorname{n}: \operatorname{Nat}, \operatorname{recurrenceFunction} \operatorname{u} \operatorname{n} = (\operatorname{sInf} (\operatorname{recurrenceCandidates} \operatorname{u} \operatorname{n}))$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.recurrenceFunction` (`✓ std3`).

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

Printed p. 706, Section 3: “R(n) = inf{N ∈ N : ∀w ∈ Lᴺ(u), Lₙ(w) = Lₙ(u)} ∈ N ∪ {+∞}”. The candidate set consists of finite natural bounds embedded in ENat; its empty infimum is top.

**Definition 1.10 (recurrenceRatio).**

$$\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \forall \operatorname{n}: \operatorname{Nat}, \operatorname{recurrenceRatio} \operatorname{u} \operatorname{n} = (\operatorname{if} \operatorname{n} = 0 \operatorname{then} 0 \operatorname{else} (\operatorname{r} : \operatorname{ENat} \mapsto (\operatorname{r} : \operatorname{ENNReal})) (\operatorname{recurrenceFunction} \operatorname{u} \operatorname{n}) / (\operatorname{n} : \operatorname{ENNReal}))$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.recurrenceRatio` (`✓ std3`).

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

The displayed definition uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Definition 1.11 (rhoStar).**

$$\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \operatorname{rhoStar} \operatorname{u} = (\operatorname{iInf}\left((n0:\operatorname{Nat}\mapsto\operatorname{iSup}\left((n:\operatorname{Nat}\mapsto\operatorname{if} \operatorname{n0} \leq \operatorname{n} \operatorname{then} \operatorname{recurrenceRatio} \operatorname{u} \operatorname{n} \operatorname{else} 0)\right))\right))$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.rhoStar` (`✓ std3`).

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

Printed p. 706, Section 3: “ρ*(u) = lim supₙ→∞ R(n)/n ∈ [1, +∞].” The zero branch pads indices below the tail.

**Definition 1.12 (floorCoding).**

$$\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \forall alpha: \operatorname{Real}, \forall beta: \operatorname{Real}, \operatorname{floorCoding} \operatorname{u} alpha beta = (\forall \operatorname{n} : \operatorname{Nat} , \operatorname{u} \operatorname{n} = \operatorname{true} \iff \lfloor alpha \cdot (\operatorname{n} : \operatorname{Real}) + beta \rfloor = \lfloor alpha \cdot ((\operatorname{n} + 1 : \operatorname{Nat}) : \operatorname{Real}) + beta \rfloor)$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.floorCoding` (`✓ std3`).

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

The displayed definition uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Definition 1.13 (ceilCoding).**

$$\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \forall alpha: \operatorname{Real}, \forall beta: \operatorname{Real}, \operatorname{ceilCoding} \operatorname{u} alpha beta = (\forall \operatorname{n} : \operatorname{Nat} , \operatorname{u} \operatorname{n} = \operatorname{true} \iff \operatorname{Int.ceil}\left(alpha \cdot (\operatorname{n} : \operatorname{Real}) + beta\right) = \operatorname{Int.ceil}\left(alpha \cdot ((\operatorname{n} + 1 : \operatorname{Nat}) : \operatorname{Real}) + beta\right))$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.ceilCoding` (`✓ std3`).

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

The displayed definition uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Definition 1.14 (IsSturmian).**

$$\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \operatorname{IsSturmian} \operatorname{u} = (\exists alpha beta : \operatorname{Real} , \operatorname{Irrational} alpha \land alpha \in \operatorname{Set.Icc} 0 1 \land (\operatorname{floorCoding} \operatorname{u} alpha beta \lor \operatorname{ceilCoding} \operatorname{u} alpha beta))$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.IsSturmian` (`✓ std3`).

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

Printed p. 702: “A word u ∈ Bᴺ is called a Sturmian word of slope α when there exists β ∈ R such that one of the following holds: (i) for all n ∈ N, uₙ = a if and only if ⌊αn + β⌋ = ⌊α(n + 1) + β⌋; (ii) for all n ∈ N, uₙ = a if and only if ⌈αn + β⌉ = ⌈α(n + 1) + β⌉.” The slope is irrational and lies in the closed unit interval.

**Definition 1.15 (replicated).**

$$\forall \operatorname{k}: \operatorname{Nat}, \forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \forall \operatorname{n}: \operatorname{Nat}, \operatorname{replicated} \operatorname{k} \operatorname{u} \operatorname{n} = \operatorname{u} (\operatorname{Nat.div} \operatorname{n} \operatorname{k})$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.replicated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.16 (vk not sturmian).**

$$\forall \operatorname{k}: \operatorname{Nat}, (2 \leq \operatorname{k})\Rightarrow\neg \operatorname{IsSturmian} ((\operatorname{replicated} \operatorname{k} \operatorname{D5.S1.Words.goldenWord}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.vk_not_sturmian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.17 (contains block iff).**

$$\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \forall \operatorname{v}: \operatorname{Nat} \to \operatorname{Bool}, \forall \operatorname{i}: \operatorname{Nat}, \forall \operatorname{j}: \operatorname{Nat}, \forall \operatorname{n}: \operatorname{Nat}, \forall \operatorname{N}: \operatorname{Nat}, \operatorname{List.IsInfix} ((\operatorname{rayPrefix} (\operatorname{index} \mapsto \operatorname{u} (\operatorname{i} + \operatorname{index})) \operatorname{n})) ((\operatorname{rayPrefix} (\operatorname{index} \mapsto \operatorname{v} (\operatorname{j} + \operatorname{index})) \operatorname{N})) \iff \exists \operatorname{t} , \operatorname{t} + \operatorname{n} \leq \operatorname{N} \land \forall \operatorname{r} < \operatorname{n} , \operatorname{u} (\operatorname{i} + \operatorname{r}) = \operatorname{v} (\operatorname{j} + (\operatorname{t} + \operatorname{r}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.contains_block_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.18 (replicated transition aligned).**

$$\forall \operatorname{k}: \operatorname{Nat}, \forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \forall \operatorname{i}: \operatorname{Nat}, (\operatorname{replicated} \operatorname{k} \operatorname{u} \operatorname{i} \neq \operatorname{replicated} \operatorname{k} \operatorname{u} (\operatorname{i} + 1))\Rightarrow\operatorname{k} \mid \operatorname{i} + 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.replicated_transition_aligned` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.19 (rhoStar eq limsup).**

$$\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \operatorname{rhoStar} \operatorname{u} = \operatorname{Filter.limsup} (\operatorname{recurrenceRatio} \operatorname{u}) \operatorname{Filter.atTop}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.rhoStar_eq_limsup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.20 (rhoStar replicated).**

$$\forall \operatorname{k}: \operatorname{Nat}, (0 < \operatorname{k})\Rightarrow\forall \operatorname{u}: \operatorname{Nat} \to \operatorname{Bool}, \operatorname{rhoStar} (\operatorname{replicated} \operatorname{k} \operatorname{u}) = \operatorname{rhoStar} \operatorname{u}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.rhoStar_replicated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

## References

- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.HasPeriod`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.HasRecurrenceBound`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.IsSturmian`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.ceilCoding`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.contains_block_iff`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.exponent`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.factorLanguage`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.floorCoding`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.indStar`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.indexAt`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.per`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.recurrenceCandidates`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.recurrenceFunction`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.recurrenceRatio`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.replicated`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.replicated_transition_aligned`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.rhoStar`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.rhoStar_eq_limsup`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.rhoStar_replicated`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneRecurrenceTransport.vk_not_sturmian`
- Dependency: [D5/S0/Computability/Coding/BiasedMassFrontier](../../../S0/Computability/Coding/BiasedMassFrontier.md)
- Dependency: [D5/S1/Words/Complexity/MorseHedlund](MorseHedlund.md)
- Dependency: [D5/S1/Words/GoldenSubstFixed](../GoldenSubstFixed.md)
- Dependency: [D5/S1/Words/GoldenWord](../GoldenWord.md)
- Dependency: [D5/S1/Words/Mechanical/MechanicalBalance](../Mechanical/MechanicalBalance.md)
