---
bibkey: kolassali2010saddlepoint
authors: John Kolassa and Jixin Li
year: 2010
title: Multivariate saddlepoint approximations in tail probability and conditional inference
doi: 10.3150/09-BEJ237
url: https://arxiv.org/abs/1011.5775v1
claim: "Section 4 derives conditional tail approximations by jointly approximating the inversion numerator and its marginal-density denominator; the introduction specifies relative order inverse sample size on admissible compact sets."
strata_touched: []
license: citation-only
triage: anchor
---

# Conditional saddlepoints require a common denominator

## Verified locator

DOI: <https://doi.org/10.3150/09-BEJ237> resolves to Project Euclid,
whose response contains no readable article text. Firecrawl returns
HTTP 402. Crossref identifies the authors and *Bernoulli* 16(4),
1191–1207. The accessible [arXiv reprint](https://arxiv.org/abs/1011.5775v1),
HTTP 200, prints the same journal coordinates and DOI, with archive
stamp 26 November 2010. Its 18-page PDF's introduction, section 2,
and section 4, including equation (4.1), Lemma 4.1, denominator
relation (4.3) and lattice expression (4.8), were inspected.
Printed pp. 1201–1204 correspond to PDF pp. 11–14.

## Classical conditional approximation mechanism

The model is the mean of iid random vectors of fixed dimension.
For continuous variables, a conditional tail at $t_B$ is represented
by

$$
\frac{\displaystyle\int_{y_A\ge t_A} f_T(y_A,t_B)\,dy_A}
{f_{T_B}(t_B)},\qquad f_{T_B}(t_B)>0.
$$

Equation (4.1) writes the numerator as a complex inversion integral.
Lemma 4.1 uses a Watson expansion in the conditioning coordinates;
equation (4.3) approximates the same marginal-density denominator.
The introduction states relative error $O(n^{-1})$ on admissible
compact sets. This retains the source's cumulant-generating-function,
saddlepoint regularity and contour conditions. Lattice variables
use their own inversion factors, as in equation (4.8), rather than
substituting a continuous density at an atom.

## Scope of the original posterior application

Section 119 of the
[spectral-boundary volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
uses this numerator-and-denominator method as an antecedent.
Its count arrays grow in dimension and its fixed-size posterior
has a shared normalizer. The classical fixed-dimension theorem does
not supply uniform second derivatives in a changing Rényi order,
joint charge/information moments, or a bound for the actual
conditioning denominator at those scales.

For the arithmetic small ball, controlling an auxiliary likelihood
numerator alone cannot establish the conditional probability of the
complete calibrated posterior center. The actual kernel, positive
conditioning mass and common response must be controlled together.
Neither the conditional saddlepoint formula nor its relative-error
order supplies the native modulo-one bound.
