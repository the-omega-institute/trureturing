---
bibkey: coffey2015somosseries
authors: Mark W. Coffey
year: 2015
title: Integral representations of functions and Addison-type series for mathematical constants
doi: 10.1016/j.jnt.2015.04.005
url: https://arxiv.org/abs/1006.2551v1
claim: "Proposition 5(b), equation (1.25), at t=2 gives sum_{k>=1}(2 Li_k(1/2)-1)/k = log(sigma_2), where sigma_2 is the Somos constant."
strata_touched:
  - D5/S1/Recurrence/LerchSomosLimit
license: citation-only
triage: anchor
---

# Coffey's Somos polylogarithm series

The original preprint is arXiv:1006.2551v1, submitted June 13, 2010.
The journal citation is Journal of Number Theory 157 (2015), 79--98.
The note's year and DOI identify that later publication; the mathematical
locator below belongs to the original preprint, not an inspected journal copy.

For t>1, equation (1.23) defines sigma_t=product_{n>=1}n^{1/t^n}.
Proposition 5(b), the second series in equation (1.25), states
log(sigma_t)=(1/(t-1))*sum_{k>=1}(t Li_k(1/t)-1)/k.
At t=2 this is the known identity used to evaluate G(1) in the LP proof.
It is not an assertion that Meijer's LP sequence converges.

## Verified locator

- DOI: 10.1016/j.jnt.2015.04.005.
- Original version: https://arxiv.org/abs/1006.2551v1;
  source: https://arxiv.org/src/1006.2551v1.
- Proposition 5(b), equation (1.25); proof equations (2.19)--(2.26).
  Equation (2.19) identifies the logarithmic constant series; (2.23)
  rearranges and telescopes the alternating polylogarithm series, then
  states that the other series in (1.25) is obtained similarly.
  Equations (2.24)--(2.26) give the alternative integral argument.
- Original compressed source SHA-256:
  `ed4d33bcd15ce3820c8b394efe09843690c3d66135835f26a1e1c6eb536ffd91`.
  Its decompressed TeX was inspected at these locators. The arXiv abstract
  identifies the author, title and submission date; publisher coredata
  confirms the title, journal, year and DOI. The journal version of record
  was not inspected; no journal equation-number claim is made.
