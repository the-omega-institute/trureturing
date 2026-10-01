---
bibkey: kaliski2017targeted
authors: Burton S. Kaliski Jr.
year: 2017
title: Targeted Fibonacci Exponentiation
url: https://arxiv.org/abs/1711.02491v1
claim: Every modular Hofstadter G coefficient pair has a bounded solution and a Zeckendorf representation of logarithmic length.
strata_touched: []
license: citation-only
triage: anchor
---

# Modular Hofstadter G pairs

## Verified locator

Burton S. Kaliski Jr., *Targeted Fibonacci Exponentiation*,
arXiv:1711.02491v1, https://arxiv.org/pdf/1711.02491v1.
Appendix B, printed pages 19–22, defines the modular Hofstadter G problem.
Lemma 5 supplies the golden-ratio interval construction on pages 19–20.
Theorem 2 on pages 20–21 gives a solution with the bound
`v <= F_(2h+2)-2` whenever the modulus `r < phi^h`.
Corollary 2 on page 21 bounds its Zeckendorf representation by `2h` bits.
Theorem 3 and Figure 10 on pages 21–22 give the solving algorithm.

## Claim and scope

For any positive modulus r and prescribed residues s,t, the problem asks
for nonnegative u,v with `u=G(v)`, `u=s mod r` and `v=t mod r`.
Here `G(v)=floor((v+1)/phi)`. Thus simultaneous realization of the
unshifted Fibonacci sum and its shifted companion, and the logarithmic
Zeckendorf length of a realizing integer, are literature-attested.

The short common coefficient theorem uses a shifted rational grid with
`q=F_j`, where j is the first index with `F_j>2H`, and obtains the positive
range `H<=n<H(q+1)`. These particular constants are a refinement of the
same construction. The five-window alphabet, the first two zero bits,
removal of terminal whole zero windows, and positive canonical End after
an arbitrary actual legal prefix are additional literal-language claims.
They are not assertions of Theorem 2 or Corollary 2 in this source.
