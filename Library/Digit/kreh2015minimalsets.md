---
bibkey: kreh2015minimalsets
authors: Martin Kreh
year: 2015
title: "Minimal Sets, Journal of Integer Sequences 18 (2015), Article 15.5.3"
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL18/Kreh/kreh2.pdf
claim: "Definition 16. For a given set M ⊂ N define a sequence δⁿ(M) of sets recursively by δ⁰(M) := M, δ(M) := δ¹(M) := M \\ S(M), δⁿ⁺¹(M) := δ(δⁿ(M)) and let ηⁿ(M) := |S(δⁿ(M))|, η(M) := η¹(M). Conjecture 18. There are only countably many infinite sets M ⊂ N with η(M) ≤ η⁰(M). For all other sets we have ηⁿ(M) → ∞."
strata_touched:
  - D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation
  - D5/S1/Digit/KrehMinimalSetCountabilityRefutation
license: citation-only
triage: anchor
---

# Kreh's minimal sets

Kreh orders positive integers by decimal-string subsequence: `x ⊳ y` means
that the decimal string of `x` is obtained from that of `y` by deleting zero
or more digits. The set `S(M)` consists of the elements of `M` that are
minimal for this order.

## Verified locator

- URL: https://cs.uwaterloo.ca/journals/JIS/VOL18/Kreh/kreh2.pdf
- Publisher PDF: page 14.
- Publisher TeX: https://cs.uwaterloo.ca/journals/JIS/VOL18/Kreh/kreh2.tex
- Definition 16 (Unicode transcription, preserving the printed superscripts): Definition 16. For a given set M ⊂ N define a sequence δⁿ(M) of sets recursively by δ⁰(M) := M, δ(M) := δ¹(M) := M \ S(M), δⁿ⁺¹(M) := δ(δⁿ(M)) and let ηⁿ(M) := |S(δⁿ(M))|, η(M) := η¹(M).
- Conjecture 18 (Unicode transcription, preserving the printed superscripts): Conjecture 18. There are only countably many infinite sets M ⊂ N with η(M) ≤ η⁰(M). For all other sets we have ηⁿ(M) → ∞.

Here `N` denotes the positive integers, `x ⊳ y` is the decimal-string
subsequence order, and `S(M)` is the set of its minimal elements in `M`.
The divergence result in `KrehMinimalSetLayerGrowthRefutation` refutes the
second sentence: the set
`M* = {1, 10, 11} ∪ {110·10ʲ : j ≥ 0}` has successive minimal-layer sizes
`1, 2, 1, 1, ...`.

## Countability sentence

The companion theorem
`D5/S1/Digit/KrehMinimalSetCountabilityRefutation.result` refutes the first
sentence for the same decimal-subsequence definitions. It states

```lean
¬ Set.Countable {M : Set ℕ |
  (∀ n ∈ M, 0 < n) ∧ M.Infinite ∧ eta M 1 ≤ eta M 0}
```

Kreh's Theorem 14 and Example 15 already give the two-seed chain mechanism;
Example 17 explicitly exhibits minimal-layer sizes `2, 1, 1, ...`. The
additional argument is the powerset encoding and its uncountability
deduction, not the original two-seed mechanism.

For arbitrary `A : Set ℕ`, set `u(j)=16·10ʲ`,
`T_A={u(2n) : n ∈ ℕ} ∪ {u(2n+1) : n ∈ A}`, and `F_A={1,6} ∪ T_A`.
The exact equalities `minimal F_A={1,6}` and
`minimal (peel F_A 1)={16}` give finite layer sizes 2 and 1. Every member
is positive, and the mandatory even indices make every `F_A` infinite.
The equivalence `u(2j+1) ∈ F_A ↔ j ∈ A` makes `A ↦ F_A` injective.
An assumed natural-number encoding of the displayed collection would
therefore inject `Set ℕ` into `ℕ`, contrary to Cantor's theorem.

This is an additional clause of
`Problems/kreh-2015-minimal-sets-conjecture-18.md`, whose existing formal
resolution binding remains anchored to the divergence theorem. It does not
constitute a second distinct published question.

## Literature scope

The 2015 source statement and its two-seed construction are
literature-attested; the explicit powerset deduction above is repo-derived.
The complete supplied text of Baoulina, Kreh and Steuding's *Deleting Digits*,
arXiv:1607.01548v1 (2016), contains no explicit resolution of Conjecture 18
or its countability sentence. Its structural section concerns unions and
intersections of minimal sets. The 2017 version of record is identified by
DOI 10.1017/mag.2017.6, but its publisher PDF returned HTTP 403; its full
contents remain `ASSUMED-UNVERIFIED`. The negative finding is limited to the
texts read, and neither historical novelty nor first-publication priority
is certified.
