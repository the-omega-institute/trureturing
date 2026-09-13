---
bibkey: kreh2015minimalsets
authors: Martin Kreh
year: 2015
title: "Minimal Sets, Journal of Integer Sequences 18 (2015), Article 15.5.3"
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL18/Kreh/kreh2.pdf
claim: "Definition 16. For a given set M ⊂ N define a sequence δⁿ(M) of sets recursively by δ⁰(M) := M, δ(M) := δ¹(M) := M \\ S(M), δⁿ⁺¹(M) := δ(δⁿ(M)) and let ηₙ(M) := |S(δⁿ(M))|, η(M) := η₁(M). Conjecture 18. There are only countably many infinite sets M ⊂ N with η(M) ≤ η₀(M). For all other sets we have ηₙ(M) → ∞."
strata_touched:
  - D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation
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
- Definition 16 (verbatim): Definition 16. For a given set M ⊂ N define a sequence δⁿ(M) of sets recursively by δ⁰(M) := M, δ(M) := δ¹(M) := M \ S(M), δⁿ⁺¹(M) := δ(δⁿ(M)) and let ηₙ(M) := |S(δⁿ(M))|, η(M) := η₁(M).
- Conjecture 18 (verbatim): Conjecture 18. There are only countably many infinite sets M ⊂ N with η(M) ≤ η₀(M). For all other sets we have ηₙ(M) → ∞.

Here `N` denotes the positive integers, `x ⊳ y` is the decimal-string
subsequence order, and `S(M)` is the set of its minimal elements in `M`.
Only the second, divergence sentence is refuted: the set
`M* = {1, 10, 11} ∪ {110·10ʲ : j ≥ 0}` has successive minimal-layer sizes
`1, 2, 1, 1, ...`; the countability sentence is untouched.
