---
bibkey: bajnokbeatty2024cayleydiameteroriginal
authors: B. Bajnok and W. K. Beatty
year: 2024
title: On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups
doi: null
url: https://arxiv.org/abs/2406.04045v1
claim: Original Conjecture 1.6 states the sharp maximum order for finite noncyclic abelian groups with a signed two-element spanning set, and Theorem 1.7 supplies its lower constructions; Conjecture 4.1 gives the four-clause classification for Z2 times Z2k, with the order bound and low regimes in Theorems 4.2–4.4.
strata_touched:
  - D5/S3/FiniteGroups/BajnokBeattyAllRegimes
  - D5/S3/FiniteGroups/BajnokBeattySharpMaximum
license: citation-only
triage: anchor
---

# On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups

Béla Bajnok and W. Kyle Beatty, arXiv:2406.04045v1, 6 June 2024, Section 4.

Conjecture 4.1 asks for an exact classification of positive integers $k,s$ for which $\mathbb Z_2\times\mathbb Z_{2k}$ has an $s$-spanning set of size two. The four cases are odd $s$ with $2k\le s^2-1$; even $s$ with $2k\le s^2-s$; $s\equiv0\pmod4$ and even $k$ in $s^2-s<2k\le s^2$; and $s\equiv2\pmod4$, $k\equiv2\pmod4$ in the same strict top strip.

Theorem 4.2 proves the order bound $2k\le s^2$. Theorem 4.3 proves the odd regime, and Theorem 4.4 proves sufficiency in the even low regime. These are literature-attested inputs, without a novelty claim. The Lean full endpoint combines their formal counterparts with the repository's top-strip necessity and uniform sufficient construction.

Conjecture 1.6 concerns every natural radius $s\ge3$ and every finite noncyclic abelian group admitting a signed spanning set of size two. Its maximum is $2s^2$ if $2s+1$ is prime, and $2s^2+2s-(p^2-1)/2$ otherwise, where $p$ is the least prime factor of $2s+1$. Its stated uniform consequence is $|G|\le2s^2+2s-4$. The radius-two parenthetical is separate from this range.

Theorem 1.7 supplies the known attaining lower families. The baseline uses $\mathbb Z_s\times\mathbb Z_{2s}$ with pair $(1,1),(0,1)$. Writing $2s+1=p(2t+1)$ in the composite case gives $\mathbb Z_p\times\mathbb Z_{2pt(t+1)}$ with pair $(1,t),(1,t+1)$. The formal maximum theorem credits these lower constructions and combines their actual covers with the repository's universal upper endpoint; it makes no current literature novelty claim.

The source comparison is restricted to the original v1. Later versions and publications are not assessed, and no priority claim is made.

## Verified locator

Source: https://arxiv.org/abs/2406.04045v1

Full text: https://arxiv.org/html/2406.04045v1
