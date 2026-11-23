---
bibkey: chen2025lowautomaticcomplexity
authors: Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan
year: 2025
title: Languages of Words of Low Automatic Complexity Are Hard to Compute
doi: 10.48550/arXiv.2510.07696
url: https://arxiv.org/abs/2510.07696v1
claim: Question 5.1 asks whether the prime-alphabet lower bounds for Lq and its complement extend to arbitrary alphabets with the original Boolean circuit definition.
strata_touched:
  - D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure
  - D5/S3/Combinatorics/AutomataCircuits/LowAutomaticComplexityCircuitLowerBound
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2510.07696

Source: https://arxiv.org/abs/2510.07696v1

The v1 PDF is https://arxiv.org/pdf/2510.07696v1. The conference version is
FSTTCS 2025, DOI 10.4230/LIPIcs.FSTTCS.2025.24. Its corresponding question is
Question 47 on printed page 24:17.

## Source statements

Question 5.1, arXiv v1 p. 19:

> Do the results from Theorem 4.9 apply to arbitrary alphabets using the definition of ⊕SAC⁰ given in Definition 4.4?

Definition 1.1, p. 2:

> Let x ∈ Σ∗. An automaton M exactly accepts x if M accepts x, and whenever both y ≠ x and |y| = |x| then M rejects y.

Definition 1.6, p. 3:

> Let x ∈ Σ∗. The non-deterministic automatic complexity of x is
>
> Aₙₑ(x) = min{ k ∈ ℕ : there exists an NFA of k states which exactly accepts x }.

Definition 1.8, p. 3:

> For q ∈ (0,1/2), define Lq = {x ∈ Σ∗ : Aₙₑ(x) < q|x|}.

Definition 4.4, p. 16:

> A language L ⊂ {0,1}∗ is ⊕SAC⁰-recognisable if there exists a family (Ci)i<ω of Boolean circuits which recognises L and which satisfies the following:
>
> (1) Each Ci is defined over the basic set {∧, ⊕} and accepts negative literals.
>
> (2) The family (Ci)i<ω has constant depth.
>
> (3) Each Ci has unbounded fan-in-⊕ and bounded fan-in-∧.
>
> (4) Each Ci accepts words of length i.

Arithmetic interpretation, p. 16:

> To extend this equivalence beyond binary alphabets, take the field Fₚ for some prime p > 2. By interpreting (⊕, ∧) as (+, ×) mod p, we extend SAC⁰-recognisability to alphabets of prime cardinality.

## Mathematical correspondence

Words are `List Alphabet`. An epsilon-free Mathlib `NFA Alphabet (Fin k)`
with a singleton start set realizes the source's k states. Exact acceptance
compares words of the same length and permits multiple accepting paths.
The minimum is represented in `ℕ∞`; the settling result proves finite
attainment for every word. The language uses a strict rational threshold
and original-symbol length.

A finite arithmetic circuit over `ZMod p` has literal, constant, sum and
product gates. A strict level function certifies acyclicity; global bounds
apply to its levels and product fan-in. The circuit for a given length is
chosen before the input word. No size or uniformity bound is imposed.
Arithmetic encodings and Boolean blocks are constrained only on actual
encoded words; complements are taken inside `List Alphabet`.

The repository proof supplies finite-scale sparse nonempty sections using
an accepting-run repetition bound and a repeated-factor counting argument.
It does not assume Corollary 2.10 and does not state a separate density limit.
A uniform polynomial degree and a positive finite-grid support fraction
then contradict those sections. The complement transform is
`1 - P ^ (p - 1)`. Restricting each Boolean block to two codewords gives
affine bit substitutions.

## Evidence and limits

The exact experiment is in `the-omega-institute/trureturing-experiments`,
commit `8e43b321f87806b621faaf52f16659265c7fc2df`, at
`docs/reports/chen-et-al-2510.07696-question-5.1-arbitrary-alphabet-circuits/check.py`.
Its SHA-256 is `b1e88c6db3cbf86a3956dac11fd8e62536b757b3cabf59b65e89f4e2d285204c`.
The preregistration issue #26742 and the binding probe report exit 0 with
`ALL_CHECKS_OK`: 411 cyclic witnesses, 25,612 polynomial/grid cases,
620 alphabet comparisons and 70 ordered Boolean codeword pairs.
These are reported experiment readings, not a fresh experiment run or a
proof of the unbounded statement.

Literature completeness is ASSUMED-UNVERIFIED. The bounded source and
citation screen in #26742 identified no settlement; unread manuscripts,
provider limits and unknown citing works remain outside that reading.
No endpoint q = 1/2 result, growing-depth or growing-product-fan-in result,
or separate density-limit theorem is claimed.
