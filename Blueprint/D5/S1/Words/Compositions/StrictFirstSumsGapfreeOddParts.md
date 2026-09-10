# Strict First Sums and Gapfree Odd Parts

## Abstract

Strict zero-prepended first sums correspond to gapfree odd partitions of the same weight.

The formal target is the combinatorial bridge in OEIS A392707. Reversed partitions have their positive parts sorted increasingly. The zero-based alternating recurrence starts at zero and is inverted by the existing adjacent-sums function. Both combinatorial classes include the empty partition. The A053251 mock theta coefficient identity is not formalized here; its constant term is zero, whereas these counts start at one.

**Definition 1.1 (Strict source predicate).**

$$\forall y: \operatorname{List}\left(\mathbb{N}\right), \operatorname{IsStrictFirstSums}\left(y\right) \iff (\exists s: \operatorname{List}\left(\mathbb{N}\right), \operatorname{Pairwise}\left((a, b \mapsto a < b), s\right) \land (\forall x: \mathbb{N}, x \in s \implies 0 < x) \land \operatorname{firstSums}\left(\operatorname{cons}\left(0, s\right)\right) = y)$$

*Formalization.* `D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.IsStrictFirstSums` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2026). *OEIS A392707*. URL: <https://oeis.org/A392707>.

*Commentary.*

A positive list s is strictly increasing, and the existing firstSums applied to zero prepended to s gives y. This strengthens the sibling's weak predicate without redefining it or the adjacent-sums function.

**Definition 1.2 (Exact odd support).**

$$\forall m: \operatorname{Multiset}\left(\mathbb{N}\right), \operatorname{GapfreeOdd}\left(m\right) \iff (\exists k: \mathbb{N}, \forall x: \mathbb{N}, (x \in m \iff (\exists i: \mathbb{N}, i < k \land x = 2i+1)))$$

*Formalization.* `D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.GapfreeOdd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2026). *OEIS A392707*. URL: <https://oeis.org/A392707>.

*Commentary.*

The support equals the first k positive odd numbers. The equivalence in the formula requires both absence of other parts and presence of every listed part. The witness k=0 gives the empty multiset.

**Theorem 1.3 (The weight-preserving restriction).**

$$\forall n: \mathbb{N}, \operatorname{card}\left(\operatorname{filter}\left((p \mapsto \operatorname{IsStrictFirstSums}\left(\operatorname{sort}\left(\operatorname{parts}\left(p\right), (a, b \mapsto a \le b)\right)\right)), (\operatorname{univ}\left(\right): \operatorname{Finset}\left(\operatorname{Partition}\left(n\right)\right))\right)\right) = \operatorname{card}\left(\operatorname{filter}\left((p \mapsto \operatorname{GapfreeOdd}\left(\operatorname{parts}\left(p\right)\right)), (\operatorname{univ}\left(\right): \operatorname{Finset}\left(\operatorname{Partition}\left(n\right)\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.card_strictFirstSums_eq_gapfreeOdd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2026). *OEIS A392707*. URL: <https://oeis.org/A392707>.

*Commentary.*

Reuse the frozen sibling's firstOddEquiv, its inverse and its sum theorem. A column of height h exists exactly when row lengths drop strictly from row h-1 to row h. Thus strict row lengths are equivalent to all positive column heights up to the maximum occurring. The existing oddify map takes h to 2h-1, giving exact initial odd support. Restrict the original equivalence to this property and to total weight n, and transport via the original list/partition equivalences. No extra hypothesis is needed.

The sibling's auxiliaries are private in a legacy Lean module. A local elaborator resolves their unique original constants in the imported environment, so their definitions and proofs are reused verbatim by reference. This is an explicit dependency on that frozen private API. A053251 itself already states the gapfree odd interpretation and the psi series expansion; connecting the count to that series in Lean remains outside this module.

## References

- Truth anchor: `D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.GapfreeOdd`
- Truth anchor: `D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.IsStrictFirstSums`
- Truth anchor: `D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.card_strictFirstSums_eq_gapfreeOdd`
- Dependency: [D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts](ZeroPrependedFirstSumsOddParts.md)
