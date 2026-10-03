---
bibkey: grandjean2012threesystems
authors: B. Grandjean; Y.-C. Liang; J.-D. Bancal; N. Brunner; N. Gisin
year: 2012
title: "Bell inequalities for three systems and arbitrarily many measurement outcomes"
doi: 10.1103/PhysRevA.85.052113
url: https://arxiv.org/abs/1204.3829v2
claim: "The local-bound clause of the conjecture on (B1): the deterministic minimum is 6(K-1) for every K >= 2. The facet clause is separate."
strata_touched:
  - D5/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound
license: citation-only
triage: anchor
---

# Bell inequalities for three systems and arbitrarily many measurement outcomes

Appendix B, PDF p. 5, states:

> A possible symmetric generalization of Sliwa’s 7th inequality [46] to an
> arbitrary number of outputs reads as:
>
> 2⟨[A_1 + B_1 + C_1]_K⟩ + 2⟨[−A_1 − B_1 − C_1 − 1]_K⟩
> + ⟨[−A_1 − B_1 − C_1]_K⟩ + 3⟨[−A_2 − B_2 − C_2 − 1]_K⟩
> + ⟨[A_2 + B_2 + C_2 − 1]_K⟩ + ⟨[A_2 + B_2 + C_2]_K⟩
> + ⟨[−A_2 + B_1 + C_1]_K⟩ + ⟨[−A_1 + B_2 + C_2]_K⟩ + ⋄
> ≥ 6(K − 1), (B1)

The conjecture sentence continues on PDF p. 6:

> We conjecture that both the local bound and the facet-defining property of
> inequality (B1) hold for general K.

Section II, PDF p. 2, states fact 1:

> It suffices to consider deterministic classical strategies for determining
> the minimal value of S^{(K)} allowed in a local theory

In a deterministic strategy, the expectation of a bracket is its least
nonnegative residue. Appendix A defines the permutation symbol through:

> missing terms which must be added to ensure that the inequality is
> symmetrical with respect to arbitrary permutation of parties.

With `a,b,c` representing first-setting outputs and `A,B,C` second-setting
outputs, the six mixed terms are `[-A+b+c]_K`, `[-B+a+c]_K`,
`[-C+a+b]_K`, `[-a+B+C]_K`, `[-b+A+C]_K` and `[-c+A+B]_K`.
The Lean definition `J` preserves the six pure terms and these six mixed
terms using `ZMod K` and `ZMod.val`; `claim` asserts their sharp minimum
for every `K >= 2`. Only the local-bound clause is settled. The
facet-defining property is a separate open question.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevA.85.052113
- URL: https://arxiv.org/abs/1204.3829v2
- PDF: https://arxiv.org/pdf/1204.3829v2, Section II p. 2 and Appendix B pp. 5–6.
