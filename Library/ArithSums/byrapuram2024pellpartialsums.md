---
bibkey: byrapuram2024pellpartialsums
authors: Nikhil Byrapuram; Adam Ge; Selena Ge; Tanya Khovanova; Sylvia Zia Lee; Rajarshi Mandal; Gordon Redwine; Soham Samanta; Daniel Wu; Danyang Xu; Ray Zhao
year: 2024
title: "Fibonacci Partial Sums Tricks"
doi: 10.1080/00150517.2025.2556152
url: https://arxiv.org/html/2409.01296v1
claim: "Conjecture 18: For the Pell sequence, we have m^P_{4k+1}=m^P_{4k+2}=1, m^P_{4k-1}=2k, and m^P_{4k}=2k+1."
strata_touched:
  - D5/S1/Recurrence/PellPartialSumMaxIndex
license: citation-only
triage: anchor
---

# Pell partial sums and their greatest dividing indices

Byrapuram et al., *Fibonacci Partial Sums Tricks*, arXiv:2409.01296v1
(2 September 2024), Section 4.5, states:

> **Conjecture 18.** For the Pell sequence, we have
> m^P_{4k+1}=m^P_{4k+2}=1, m^P_{4k-1}=2k, and m^P_{4k}=2k+1.

The paper defines the Pell sequence by `P(0)=0`, `P(1)=1` and
`P(n+2)=2P(n+1)+P(n)`. Its notation `S_n^P` is the sum of the first
`n` terms starting at index one, and `m_n^P` is the greatest positive
index whose Pell term divides that sum. The classes `4k+1` and `4k+2`
use all `k>=0`; the classes `4k-1` and `4k` use `k>=1`, so their sums
are nonempty. The formal statement uses `IsGreatest` and the existing
Pell definitions in `D5/S1/Recurrence/PellCompanionGcd`.

The journal DOI is `10.1080/00150517.2025.2556152`, in *The Fibonacci
Quarterly*. OpenAlex reports its online publication date as 24 June
2026. The arXiv API returns v1 as the current version. The HTML source
contains Conjecture 18 in Section 4.5 and cites Bradie 2010 and Falcón
Santana–Díaz-Barrero 2006 for the two even-class partial-sum identities.

Bradie, *Extensions and Refinements of Some Properties of Sums
Involving Pell Numbers*, *Missouri Journal of Mathematical Sciences*
22(1) (2010), 37–43, DOI `10.35834/mjms/1312232719`, has an abstract
describing square characterizations of initial sums and divisibility
properties. Its full text was not accessible in the checked endpoints;
the abstract does not resolve the greatest-index question.

## Verified locator

- https://arxiv.org/html/2409.01296v1 : Section 4.5, Conjecture 18,
  sequence convention and references; retrieved 2026-10-03.
- https://export.arxiv.org/api/query?id_list=2409.01296 : current entry
  `2409.01296v1`; retrieved 2026-10-03.
- https://doi.org/10.1080/00150517.2025.2556152 : journal DOI;
  bibliographic metadata checked through OpenAlex on 2026-10-03.
- https://api.openalex.org/works/https://doi.org/10.1080/00150517.2025.2556152 :
  work W4402954534, cited-by count 0; retrieved 2026-10-03.
- https://api.openalex.org/works?filter=cites:W4402954534 : zero indexed
  citing works; retrieved 2026-10-03. This is an index result, not an
  exhaustive assertion about all subsequent literature.
- https://api.openalex.org/works/https://doi.org/10.35834/mjms/1312232719 :
  Bradie metadata and abstract; retrieved 2026-10-03.

The bounded prior-work check in issue #12462 and these sources do not
establish publication priority or global absence of a prior resolution.
