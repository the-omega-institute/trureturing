# Halving partitions and unrestricted finite integer families

## Abstract

The exact halving-partition count admits no finite integral family closed under both decimations.

The historical integer result remains declared_validated. The full arbitrary-ring audit compiles its realization, variation, sensitivity and dependence proofs, but current source binding is declared_unresolved with IE-C050 source.dictionary_or_proof_coordinate. Newly exposed supplier audits are unfinished. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.

Alekseyev's Halving Partitions and Hyperbinary Expansions, arXiv:2611.01243v1, Definition 1 and section 6, supplies the source count and asks whether it is 2-regular. The source objects here are actual ordered lists of positive integers. The virtual predecessor is the total n. Every finite length is admitted, repeated entries remain distinct list positions, and terminal ones may repeat. At zero the only object is the empty list.

**Definition 1.1 (The two possible values of a half).**

$$\forall p \in \mathrm{Nat},\; \forall q \in \mathrm{Nat},\; \operatorname{IsHalf}\left(p, q\right) \Leftrightarrow \left(q = \operatorname{natDiv}\left(p, 2\right) \lor q = \operatorname{natDiv}\left(p + 1, 2\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.IsHalf` (`✓ std3`).

*Citation.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

For every previous and next natural value, IsHalf is a disjunction of value equalities with the lower and upper integer halves. When previous is even the two values coincide; no choice label is stored and no object is doubled.

**Definition 1.2 (Decidability of the half-value test).**

$$instDecidableIsHalf: \forall previous \in \mathrm{Nat},\; \forall next \in \mathrm{Nat},\; \operatorname{Decidable}\left(\operatorname{IsHalf}\left(previous, next\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.instDecidableIsHalf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every previous and next natural value, this instance decides IsHalf by deciding its disjunction of equalities.

**Definition 1.3 (Successive halving along a finite list).**

$$\left(\forall p \in \mathrm{Nat},\; \operatorname{Follows}\left(p, \operatorname{nil}\left(\right)\right)\right) \land \left(\forall p \in \mathrm{Nat},\; \forall q \in \mathrm{Nat},\; \forall t \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{Follows}\left(p, \operatorname{cons}\left(q, t\right)\right) \Leftrightarrow \left(\operatorname{IsHalf}\left(p, q\right) \land \operatorname{Follows}\left(q, t\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.Follows` (`✓ std3`).

*Citation.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The empty list follows any predecessor. A nonempty list follows precisely when its first value is a half of the predecessor and its tail follows that first value. Positivity and the total are imposed separately. The recursive decider tests values and introduces no bound on the list length.

**Definition 1.4 (Decidability of finite-list halving).**

$$instDecidableFollows: \forall previous \in \mathrm{Nat},\; \forall parts \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{Decidable}\left(\operatorname{Follows}\left(previous, parts\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.instDecidableFollows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every predecessor and finite natural list, this instance decides Follows by recursion on that list, with no length restriction.

**Definition 1.5 (The independently specified source carrier).**

$$\forall n \in \mathrm{Nat},\; \operatorname{SourceLists}\left(n\right) = \{p: \operatorname{List}\left(\mathrm{Nat}\right) \mid \left(\forall x \in \mathrm{Nat},\; x \in p \Rightarrow 0 < x\right) \land \left(\operatorname{sum}\left(p\right) = n \land \operatorname{Follows}\left(n, p\right)\right)\}$$

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.SourceLists` (`✓ std3`).

*Citation.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

SourceLists(n) contains exactly the positive lists with sum n satisfying Follows(n,p). There is no maximal-chain, sorting, distinctness or final-value condition. In particular, positivity and total zero force the empty list.

**Definition 1.6 (The finite composition presentation).**

$$\forall n \in \mathrm{Nat},\; \operatorname{HalvingCompositions}\left(n\right) = \{c: \operatorname{Composition}\left(n\right) \mid \operatorname{Follows}\left(n, \operatorname{blocks}\left(c\right)\right)\}$$

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.HalvingCompositions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib's Composition n stores the same list, positivity and total. Filtering it by Follows preserves order and every repeated part. The existing finite Composition instance and the decidable filter supply a finite carrier at every n.

**Definition 1.7 (List-preserving source correspondence).**

$$\forall n \in \mathrm{Nat},\; \operatorname{sourceEquiv}\left(n\right): \operatorname{SourceLists}\left(n\right) \equiv \operatorname{HalvingCompositions}\left(n\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.sourceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map wraps the original list as a Composition and retains its Follows proof. The inverse projects that same list. Both inverse laws are proved by the constructors, so no source object is lost or identified. The transported Finite instance certifies finiteness of the independent source carrier.

**Definition 1.8 (Enumeration of halving compositions).**

$$instFintypeHalvingCompositions: \forall n \in \mathrm{Nat},\; \operatorname{Fintype}\left(\operatorname{HalvingCompositions}\left(n\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.instFintypeHalvingCompositions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural total n, the instance enumerates the subtype of Composition n satisfying Follows, using the decidable predicate.

**Definition 1.9 (Finiteness of the source-list carrier).**

$$instFiniteSourceLists: \forall n \in \mathrm{Nat},\; \operatorname{Finite}\left(\operatorname{SourceLists}\left(n\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.instFiniteSourceLists` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural total n, the source carrier is finite by transport along sourceEquiv(n) from HalvingCompositions(n).

**Definition 1.10 (The exact source count).**

$$\forall n \in \mathrm{Nat},\; \operatorname{count}\left(n\right) = \operatorname{card}\left(\operatorname{SourceLists}\left(n\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.count` (`✓ std3`).

*Citation.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The function count(n) is Nat.card of SourceLists(n), defined independently of every recurrence and of the dyadic formula used in the proof. The final theorem also identifies it with Fintype.card of HalvingCompositions(n) for all n.

**Definition 1.11 (An unrestricted integral matrix family).**

$$\forall a \in (\mathrm{Nat} \to \mathbb{Z}),\; \operatorname{MatrixFamily}\left(a\right) \Leftrightarrow \left(\exists d \in \mathrm{Nat},\; 0 < d \land \left(\exists F \in (\mathrm{Nat} \to (\operatorname{Fin}\left(d\right) \to \mathbb{Z})),\; \exists M0 \in (\operatorname{Fin}\left(d\right) \to (\operatorname{Fin}\left(d\right) \to \mathbb{Z})),\; \exists M1 \in (\operatorname{Fin}\left(d\right) \to (\operatorname{Fin}\left(d\right) \to \mathbb{Z})),\; \left(\forall n \in \mathrm{Nat},\; \operatorname{F}\left(n, 0\right) = \operatorname{a}\left(n\right)\right) \land \left(\left(\forall n \in \mathrm{Nat},\; \operatorname{F}\left(2 \cdot n\right) = \operatorname{mulVec}\left(M0, \operatorname{F}\left(n\right)\right)\right) \land \left(\forall n \in \mathrm{Nat},\; \operatorname{F}\left(2 \cdot n + 1\right) = \operatorname{mulVec}\left(M1, \operatorname{F}\left(n\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.MatrixFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dimension d ranges over every positive natural number. F is any sequence of d-dimensional integer vectors and M0,M1 are fixed integral d-by-d matrices. Every natural input, including zero, satisfies both displayed vector equalities. Coordinate zero is a. No independence, invertibility or dimension cutoff is assumed.

**Definition 1.12 (A family indexed by Fin d).**

$$\forall a \in (\mathrm{Nat} \to \mathbb{Z}),\; \operatorname{ClosedFamily}\left(a\right) \Leftrightarrow \left(\exists d \in \mathrm{Nat},\; 0 < d \land \left(\exists b \in (\operatorname{Fin}\left(d\right) \to (\mathrm{Nat} \to \mathbb{Z})),\; \exists c0 \in (\operatorname{Fin}\left(d\right) \to (\operatorname{Fin}\left(d\right) \to \mathbb{Z})),\; \exists c1 \in (\operatorname{Fin}\left(d\right) \to (\operatorname{Fin}\left(d\right) \to \mathbb{Z})),\; \left(\forall n \in \mathrm{Nat},\; \operatorname{b}\left(0, n\right) = \operatorname{a}\left(n\right)\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(d\right),\; \forall n \in \mathrm{Nat},\; \operatorname{b}\left(i, 2 \cdot n\right) = \sum_{j: \operatorname{Fin}\left(d\right)}\operatorname{c0}\left(i, j\right) \cdot \operatorname{b}\left(j, n\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(d\right),\; \forall n \in \mathrm{Nat},\; \operatorname{b}\left(i, 2 \cdot n + 1\right) = \sum_{j: \operatorname{Fin}\left(d\right)}\operatorname{c1}\left(i, j\right) \cdot \operatorname{b}\left(j, n\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.ClosedFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer sequences b(i,n) contain a at index zero. Each even and odd subsequence is a fixed integer linear combination of the same family. The coefficient functions c0 and c1 are independent of n. Equal constituent sequences and linear dependence are allowed.

**Definition 1.13 (An arbitrary finite indexed family).**

$$\forall a \in (\mathrm{Nat} \to \mathbb{Z}),\; \operatorname{ArbitraryFamily}\left(a\right) \Leftrightarrow \left(\exists I \in \mathrm{Type},\; \exists hI \in \operatorname{Fintype}\left(I\right),\; \exists b \in (I \to (\mathrm{Nat} \to \mathbb{Z})),\; \exists i0 \in I,\; \exists c0 \in (I \to (I \to \mathbb{Z})),\; \exists c1 \in (I \to (I \to \mathbb{Z})),\; \left(\forall n \in \mathrm{Nat},\; \operatorname{b}\left(i0, n\right) = \operatorname{a}\left(n\right)\right) \land \left(\left(\forall i \in I,\; \forall n \in \mathrm{Nat},\; \operatorname{b}\left(i, 2 \cdot n\right) = \sum_{j \in \operatorname{elems}\left(hI\right)}\operatorname{c0}\left(i, j\right) \cdot \operatorname{b}\left(j, n\right)\right) \land \left(\forall i \in I,\; \forall n \in \mathrm{Nat},\; \operatorname{b}\left(i, 2 \cdot n + 1\right) = \sum_{j \in \operatorname{elems}\left(hI\right)}\operatorname{c1}\left(i, j\right) \cdot \operatorname{b}\left(j, n\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.ArbitraryFamily` (`✓ std3`).

*Citation.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The index type I is any finite type, with a distinguished i0 carrying a. Here I is the Lean indexing type and hI is its Fintype witness, installed as the local instance. The expression elems(hI) is Fintype.elems, the complete finite enumeration used in both sums. It supplies no basis or algebraic independence. Different indices may carry equal sequences. The proof enumerates I by Fin(card I) and swaps i0 to zero, transporting both coefficient sums in full. Conversely every matrix family supplies such a finite family.

**Definition 1.14 (The exact negative matrix event).**

$$claim \Leftrightarrow \left(\neg \operatorname{MatrixFamily}\left((n: \mathrm{Nat} \mapsto \operatorname{Int}\left(\operatorname{count}\left(n\right)\right))\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

claim is the negation of MatrixFamily for the integer cast of the independent count, on its complete natural domain.

**Theorem 1.15 (The whole source question has a negative answer).**

$$claim \land \left(\left(\forall a \in (\mathrm{Nat} \to \mathbb{Z}),\; \operatorname{ClosedFamily}\left(a\right) \Leftrightarrow \operatorname{MatrixFamily}\left(a\right)\right) \land \left(\left(\forall a \in (\mathrm{Nat} \to \mathbb{Z}),\; \operatorname{ArbitraryFamily}\left(a\right) \Leftrightarrow \operatorname{MatrixFamily}\left(a\right)\right) \land \left(\left(\neg \operatorname{ArbitraryFamily}\left((n: \mathrm{Nat} \mapsto \operatorname{Int}\left(\operatorname{count}\left(n\right)\right))\right)\right) \land \left(\left(\forall n \in \mathrm{Nat},\; \operatorname{count}\left(n\right) = \operatorname{card}\left(\operatorname{HalvingCompositions}\left(n\right)\right)\right) \land \operatorname{count}\left(0\right) = 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.result` (`✓ std3`). ∎

*Resolves.* `Problems/alekseyev-halving-partitions-nonregularity` (refuted) by `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"alekseyev-halving-partitions-nonregularity","declaration_gid":"D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The theorem proves claim, both directions of each family/matrix equivalence for every integer sequence a, nonexistence of an arbitrary finite family for the source count, and the exact source/composition cardinality identity for every n. These are literal finite-family representations; no finite-kernel, finite-alphabet, eventual-input or basis substitute enters the statement.

**Definition 1.16 (powerWord).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.powerWord`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.powerWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: def powerWord : ℕ → ℕ → List ℕ | _, 0 => [] | 0, l + 1 => 1 :: powerWord 0 l | m + 1, l + 1 => 2 ^ m :: powerWord m l

**Definition 1.17 (oddWord).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.oddWord`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.oddWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: def oddWord : ℕ → ℕ → ℕ → List ℕ | _, _, 0 => [] | 0, _, l + 1 => 1 :: powerWord 0 l | m + 1, 0, l + 1 => 2 ^ m :: powerWord m l | m + 1, j + 1, l + 1 => (2 ^ m + 1) :: oddWord m j l

**Theorem 1.18 (powerWord_length).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.powerWord_length`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.powerWord_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: theorem powerWord_length (m l : ℕ) : (powerWord m l).length = l

**Theorem 1.19 (oddWord_length).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.oddWord_length`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.oddWord_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: theorem oddWord_length (m j l : ℕ) : (oddWord m j l).length = l

**Theorem 1.20 (odd_follows).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.odd_follows`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.odd_follows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: theorem odd_follows (m : ℕ) (p : List ℕ) (hp : ∀ x ∈ p, 0 < x) : Follows (2 ^ m + 1) p ↔ ∃ j, j ≤ m ∧ j ≤ p.length ∧ p = oddWord m j p.length

**Theorem 1.21 (powerWord_sum_short).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.powerWord_sum_short`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.powerWord_sum_short` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: theorem powerWord_sum_short (m l : ℕ) (hl : l ≤ m) : (powerWord m l).sum + 2 ^ (m - l) = 2 ^ m

**Theorem 1.22 (powerWord_sum_long).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.powerWord_sum_long`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.powerWord_sum_long` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: theorem powerWord_sum_long (m l : ℕ) (hl : m ≤ l) : (powerWord m l).sum + 1 = 2 ^ m + (l - m)

**Theorem 1.23 (oddWord_sum).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.oddWord_sum`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.oddWord_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: theorem oddWord_sum (m j l : ℕ) (hjm : j ≤ m) (hjl : j ≤ l) : (oddWord m j l).sum = (powerWord m l).sum + j

**Theorem 1.24 (dyadic_source_classification).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.dyadic_source_classification`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.dyadic_source_classification` (`✓ std3`). ∎

*Citation.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: theorem dyadic_source_classification (m : ℕ) (p : SourceLists (2 ^ m + 1)) : ∃ j, j ≤ m ∧ j ≤ p.1.length ∧ p.1 = oddWord m j p.1.length ∧ (p.1.length ≤ m → j = 2 ^ (m - p.1.length) + 1) ∧ (m ≤ p.1.length → j + (p.1.length - m) = 2)

**Theorem 1.25 (oddWord_prefix_injective).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.oddWord_prefix_injective`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.oddWord_prefix_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: theorem oddWord_prefix_injective (m l j k : ℕ) (hjm : j ≤ m) (hjl : j ≤ l) (hkm : k ≤ m) (hkl : k ≤ l) (he : oddWord m j l = oddWord m k l) : j = k

**Definition 1.26 (Threshold).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.Threshold`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.Threshold` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: abbrev Threshold (m : ℕ) := {r : Fin (m + 1) // 1 ≤ r.val ∧ 2 ^ r.val + r.val + 1 ≤ m}

**Definition 1.27 (DyadicCode).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.DyadicCode`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.DyadicCode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: abbrev DyadicCode (m : ℕ) := Fin 3 ⊕ Threshold m

**Definition 1.28 (codeParams).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.codeParams`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.codeParams` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: def codeParams (m : ℕ) : DyadicCode m → ℕ × ℕ | .inl i => if i = 0 then (m, 2) else if i = 1 then (m + 1, 1) else (m + 2, 0) | .inr r => (m - r.1.val, 2 ^ r.1.val + 1)

**Theorem 1.29 (code_bounds).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.code_bounds`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.code_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: theorem code_bounds (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) : (codeParams m c).2 ≤ m ∧ (codeParams m c).2 ≤ (codeParams m c).1

**Definition 1.30 (codeSource).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.codeSource`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.codeSource` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: def codeSource (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) : SourceLists (2 ^ m + 1) := by let l := (codeParams m c).1 let j := (codeParams m c).2 have hb := code_bounds m hm c refine ⟨oddWord m j l, oddWord_positive m j l, code_total m hm c, ?_⟩ apply (odd_follows m _ (oddWord_positive m j l)).mpr refine ⟨j, hb.1, ?_, ?_⟩ · simpa only [oddWord_length] using hb.2 · rw [oddWord_length]

**Theorem 1.31 (codeSource_bijective).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.codeSource_bijective`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.codeSource_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: theorem codeSource_bijective (m : ℕ) (hm : 2 ≤ m) : Function.Bijective (codeSource m hm)

**Theorem 1.32 (dyadic_source_count).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.dyadic_source_count`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.dyadic_source_count` (`✓ std3`). ∎

*Citation.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: theorem dyadic_source_count (m : ℕ) (hm : 2 ≤ m) : count (2 ^ m + 1) = 3 + Fintype.card {r : Fin (m + 1) // 1 ≤ r.val ∧ 2 ^ r.val + r.val + 1 ≤ m}

**Theorem 1.33 (threshold_mono).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.threshold_mono`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.threshold_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: theorem threshold_mono {r s : ℕ} (h : r ≤ s) : 2 ^ r + r + 1 ≤ 2 ^ s + s + 1

**Theorem 1.34 (dyadic_plateau).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.dyadic_plateau`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.dyadic_plateau` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.

Exact source declaration: theorem dyadic_plateau (m r : ℕ) (hm : 2 ≤ m) (hr : 1 ≤ r) (hlo : 2 ^ r + r + 1 ≤ m) (hhi : m < 2 ^ (r + 1) + (r + 1) + 1) : count (2 ^ m + 1) = 3 + r

**Theorem 1.35 (nonregularity_over).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.nonregularity_over`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.nonregularity_over` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

The actual count has no fixed binary matrix representation over every nonzero commutative unital ring, including positive characteristic and zero divisors.

Exact source declaration: theorem nonregularity_over (R : Type*) [CommRing R] [Nontrivial R] : ¬ BinaryDecimation.MatrixFamily (fun n => (count n : R))

For m at least two, every source list at total 2^m+1 has one prefix of rounded-up values followed by deterministic powers of two and, when the length exceeds m, a tail of ones. If its length l is at most m, the number j of rounded-up positions satisfies j=2^(m-l)+1. If l is at least m, it satisfies j+(l-m)=2. The exhaustive classification and uniqueness produce a bijection with three base lists of lengths m,m+1,m+2 and one additional list for each positive r satisfying 2^r+r+1≤m. Thus count(2^m+1)=3+#{r≥1:2^r+r+1≤m}. The bound r≤m used in the finite code follows from that inequality and restricts no qualifying r.

Between consecutive thresholds the dyadic count is constant. Its first difference has 2^r consecutive zero values after the threshold 2^r+r and is followed by a value one at 2^(r+1)+(r+1). A hypothetical matrix family gives the dyadic observations by applying M1 after powers of M0. Mathlib's integral Cayley–Hamilton theorem gives a monic forward recurrence of order d for them and for their differences. Choose a zero block at least that long. Mathlib's recurrence-uniqueness theorem forces the whole subsequent tail to be zero, contradicting the next one. Only forward propagation is used; the matrices may be singular.

## References

- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.ArbitraryFamily`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.ClosedFamily`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.DyadicCode`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.Follows`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.HalvingCompositions`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.IsHalf`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.MatrixFamily`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.SourceLists`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.Threshold`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.claim`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.codeParams`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.codeSource`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.codeSource_bijective`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.code_bounds`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.count`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.dyadic_plateau`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.dyadic_source_classification`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.dyadic_source_count`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.instDecidableFollows`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.instDecidableIsHalf`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.instFiniteSourceLists`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.instFintypeHalvingCompositions`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.nonregularity_over`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.oddWord`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.oddWord_length`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.oddWord_prefix_injective`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.oddWord_sum`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.odd_follows`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.powerWord`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.powerWord_length`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.powerWord_sum_long`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.powerWord_sum_short`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.result`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.sourceEquiv`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.threshold_mono`
- Dependency: [D5/S1/Recurrence/BinaryDecimation](../BinaryDecimation.md)
