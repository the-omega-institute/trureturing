---
bibkey: cheigh2022towards
authors: Justin Cheigh and Guilherme Zeus Dantas e Moura and Ryan Jeong and Jacob Lehmann Duke and Wyatt Milgrim and Steven J. Miller and Prakod Ngamlamai
year: 2022
title: Towards the Gaussianity of Random Zeckendorf Games
doi: 10.48550/arXiv.2210.11038
claim: A uniform summable strong-mixing bound on the split indicators of the random Zeckendorf game would yield a Gaussian limit for the game length.
strata_touched:
  - D5/S1/Digit/Carry
  - D5/S0/Rewriting/NewmanConfluence
  - D5/S0/Asymptotics/WeightedProbability/BinomialMomentIdentity
  - D5/S0/Asymptotics/WeightedProbability/SecondMomentCoherence
license: citation-only
triage: anchor
---

# Towards the Gaussianity of Random Zeckendorf Games

Cheigh and coauthors study the number of moves in the random Zeckendorf game.
Their Conjecture 1.7 asserts a Gaussian limit with expectation and variance
approximately `0.215N`. The paper proves Gaussianity only on certain partition
components and states that extending it to the whole space is unclear; its open
section converts that obstacle into Question 6.5, asking for a uniform summable
strong-mixing bound, and the stronger pointwise Question 6.6. An affirmative
answer to Question 6.5 yields the conjecture through a mixing central limit
theorem.

This note is the literature anchor for the problem candidate
`Problems/random-zeckendorf-game-gaussianity.md`.

## Search log

- 2026-08-18: Queried the arXiv Atom API for `id_list=2210.11038`. HTTP 200 with
  `totalResults=1`; the entry resolved to `http://arxiv.org/abs/2210.11038v1`,
  title *Towards the Gaussianity of Random Zeckendorf Games*, seven authors as
  recorded above, published 2022-10-20, primary category `math.CO`. The API
  reported no `arxiv:doi` and no `arxiv:journal_ref`, so the arXiv-assigned DOI
  is used.
- 2026-08-18: Issued `HEAD https://doi.org/10.48550/arXiv.2210.11038`, which
  returned HTTP 302 redirecting to `https://arxiv.org/abs/2210.11038`.

No literature search for a later resolution of Conjecture 1.7 or Questions
6.5/6.6 was performed; the open status recorded in the problem candidate is the
status stated in this arXiv version.

## Verified locator

- arXiv: https://arxiv.org/abs/2210.11038
- DOI: https://doi.org/10.48550/arXiv.2210.11038
