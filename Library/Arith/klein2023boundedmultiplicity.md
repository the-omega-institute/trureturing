---
bibkey: klein2023boundedmultiplicity
authors: "Jonah Klein; Dimitris Koukoulopoulos; Simon Lemieux"
year: 2023
title: "On the j-th smallest modulus of a covering system with distinct moduli"
doi: 10.48550/arXiv.2212.01299
url: https://arxiv.org/abs/2212.01299v2
claim: "The distortion method admits bounded numerical multiplicity; its second-moment proof supplies the square of that multiplicity as a leading factor."
strata_touched:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
license: citation-only
triage: anchor
---

# Distortion with bounded numerical multiplicity

The inspected primary version is [arXiv:2212.01299v2](https://arxiv.org/pdf/2212.01299v2),
23 August 2023. Page numbers below are the printed pages of that version.

Definition 2.2, p.3, defines multiplicity as the largest number of classes
having the same numerical modulus. Section 3.1, pp.3--4, explicitly adapts
the distortion construction to multiplicity greater than one. Lemma 3.2
and the proof of Lemma 3.3, pp.5--6, bound moments by tuples of original
labels. Immediately after equation (3.2), the unsimplified bound retains
a factor s^k for the kth moment of a family of multiplicity at most s.
For k=2, extending the finite exponent sums gives

    M_p^(2) <= s^2/(p-1)^2
      product_(q<p, q|Q)
        [1+(3q-1)/((1-delta_q)(q-1)^2)].

The parameters satisfy 0<=delta_q<=1/2. The estimate permits arbitrary
finite prime-power heights and requires neither squarefree moduli nor
independence of the original congruence events. The explicit Euler-factor
form uses the displayed unsimplified proof; the printed conclusion of
Lemma 3.3(b) is its weaker asymptotic simplification. This is an application
of the published proof, not a new moment theorem or a Lean result.

[Report381](../../docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/381-repeated-prime-exposure-in-missing-fibres.md)
already applies Theorem 3's minimum-modulus bound for bounded multiplicity.
[Report348](../../docs/reports/erdos7-odd-covering/profile-notes/321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md#two-multiplicity-two-covers-share-a-small-prime)
uses the explicit second moment with the independently stated numerical
continuation criterion of BBMST. Its two-cover support-intersection
conclusion is a deduction combining those tools, not a theorem attributed
verbatim to this source. No source text is vendored.
