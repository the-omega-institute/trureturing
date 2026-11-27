---
bibkey: formentikamilya2026resoca115
authors: Enrico Formenti, Supreeti Kamilya
year: 2026
title: "The Curious Case of Reversible Elementary Second Order Cellular Automaton 115"
doi: 10.4204/EPTCS.445.12
url: https://arxiv.org/abs/2606.13159v1
claim: "For RESOCA 115, in the context of finite configurations, are all multiple of 3 periods?"
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115
license: citation-only
triage: anchor
---

# Formenti and Kamilya, reversible elementary second order cellular automaton 115

The PDF byline is Enrico Formenti and Supreeti Kamilya. The arXiv and Crossref metadata spell the second surname Kamylia.

## Verified locator

- The proceedings DOI resolves to the versioned arXiv record. The PDF imprint identifies GASCom 2026, EPTCS 445, pp. 95–103. Crossref records online publication on 7 June 2026. [Proceedings DOI](https://doi.org/10.4204/EPTCS.445.12)
- arXiv records v1 submission on 11 June 2026 at 10:28:27 UTC. Equation (1) and the finite-pair definition are on printed p. 96 (PDF p. 2). Table 1, the definition of period and Question 1 are on printed p. 97 (PDF p. 3). [Versioned record](https://arxiv.org/abs/2606.13159v1) · [Versioned PDF](https://arxiv.org/pdf/2606.13159v1)
- Table 1 lists the elementary local rule bits as 0, 1, 1, 1, 0, 0, 1, 1 in neighborhood order 111, 110, 101, 100, 011, 010, 001, 000. In Equation (1), for the ordered pair of past and current binary layers on the integer line, the new past is the old current layer. The new current bit at site $i$ is the old past bit at $i$ XOR the elementary rule output from the current bits at $i-1$, $i$ and $i+1$. The model uses the full integer line. Both initial layers have finite support, with zero as the background value at initialization.

Question 1 asks

> For RESOCA 115, in the context of finite configurations, are all multiple of 3 periods?

Read period as the least positive return of the full ordered pair. The local result excludes least period nine for this two-layer update. Single-layer elementary evolution and finite cyclic lattices have different state spaces.

### Question 2 — square closure

Section 3, Question 2, on printed p. 97 (PDF p. 3) asks

> If p is a period for RESOCA 115, is p² also a period?

Section 3 defines a realized period by existence of a finite pair with that least positive return. The pair realizing the square is independently quantified. Section 2.1 on printed p. 96 defines finiteness for both layers and explicitly includes the all-zero layer among its finite configurations. [Versioned PDF, §3](https://arxiv.org/pdf/2606.13159v1#page=3)
