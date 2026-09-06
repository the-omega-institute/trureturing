---
bibkey: kotzig1964perfectonefactorization
authors: Jack Allsop and Ian M. Wanless
year: 2025
title: Perfect 1-factorisations of K_{11,11}
doi: 10.48550/arXiv.2506.02455
claim: "For every odd prime p, K_{p+1} admits a perfect one-factorization; for primes p >= 11, the cited survey identifies a family due to Kotzig as GK_{p+1}."
strata_touched:
  - D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization
license: citation-only
triage: anchor
---

# Kotzig's odd-prime family

The claim is the existence statement: for every odd prime p, the complete
graph K_{p+1} admits a perfect one-factorization. The cited survey names
Kotzig's GK_{p+1} family for primes p >= 11; this note does not extend
that identification to the small-prime cases.

The original reference is A. Kotzig, *Hamilton graphs and Hamilton circuits*,
in *Theory of Graphs and its Applications (Proc. Sympos. Smolenice, 1963)*,
Publishing House of the Czechoslovak Academy of Sciences, Prague, 1964,
pp. 63-82. That proceedings article has no DOI recorded here. The front
matter therefore identifies the DOI-bearing secondary source by Allsop and
Wanless, not Kotzig's article; its DOI and metadata are not attributed to
Kotzig.

## Verified passages

Allsop and Wanless, arXiv:2506.02455v1, Section 1, third paragraph
(`S1.p3`), state:

> There are only three known infinite families of perfect 1-factorisations
> of complete graphs [4], and these only cover graphs K_{2n} where
> 2n in {p+1, 2p} for an odd prime p.

Section 5, second paragraph (`S5.p2`), identifies the family:

> For each prime p >= 11 there are two known non-isomorphic perfect
> 1-factorisations of K_{p+1} which come from infinite families. One is due
> to Kotzig and is commonly denoted by GK_{p+1}.

This sentence both compares and names the families only in the range
p >= 11. For the smaller odd primes p = 3, 5, 7, Section 1, third paragraph
attests existence without identifying the displayed reflection family:

> Up to isomorphism there are 1, 1, 1, 1, 1, 5, 23 and 3155 perfect
> 1-factorisations of K_2, K_4, K_6, K_8, K_10, K_12, K_14 and K_16,
> respectively [6, 7, 8, 12, 14].

Thus the survey attests existence for p >= 11 and explicitly records the
remaining cases K_4, K_6, K_8. Together these cover every odd prime p.
Its bibliography entry [9] (`bib.bibx9`) supplies the original Kotzig
title, proceedings, year and pages above. Mathematical typography in the
quotations is transcribed into ASCII.

This note attests only the existence statement. The repository's
explicit construction, standalone helper statements, and Lean proof are
repository work; this note does not attribute their formulations to the
survey or to the proceedings article.

## Search log

- 2026-09-06: Retrieved the versioned HTML and checked Sections 1 and 5 and
  bibliography entry [9], including the small orders in Section 1.
- 2026-09-06: Resolved DOI 10.48550/arXiv.2506.02455: HTTP 302 to the arXiv
  abstract, then HTTP 200. Checked the authors and title against the HTML.
- 2026-09-06: Searched current origin/dev Library notes for 2506.02455 and
  kotzig1964; no existing note or duplicate DOI was found.

## Verified locator

- Secondary source: https://arxiv.org/abs/2506.02455
- Version checked: https://arxiv.org/html/2506.02455v1
- Family context: https://arxiv.org/html/2506.02455v1#S1.p3
- Family attribution: https://arxiv.org/html/2506.02455v1#S5.p2
- Kotzig reference: https://arxiv.org/html/2506.02455v1#bib.bibx9
- DOI: https://doi.org/10.48550/arXiv.2506.02455
