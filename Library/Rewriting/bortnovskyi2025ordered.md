---
bibkey: bortnovskyi2025ordered
authors: Ivan Bortnovskyi and Michael Lucas and Steven J. Miller and Iana Vranesko and Ren Watson and Cameron White
year: 2025
title: The Ordered Zeckendorf Game
doi: 10.48550/arXiv.2508.20222
claim: The Long Game Strategy is conjectured to achieve the greatest length among all legal terminating plays of the ordered Zeckendorf game.
strata_touched:
  - D5/S1/Digit/Carry
  - D5/S1/Digit/Normalize
  - D5/S0/Rewriting/NewmanConfluence
  - D5/S0/Rewriting/NormalFormFunction
license: citation-only
triage: anchor
---

# The Ordered Zeckendorf Game

Bortnovskyi, Lucas, Miller, Vranesko, Watson, and White study a variant of the
Zeckendorf game whose states are ordered lists of Fibonacci numbers, with
combine, split, and inversion-switch moves. Their Conjecture 1.7 states that the
Long Game Strategy attains the longest game length; the paper reports that this
is supported by exhaustive simulation but that a rigorous optimality proof
remains open. It also records that a full resolution of the winner was
computationally infeasible beyond `n = 25`.

This note is the literature anchor for the problem candidate
`Problems/ordered-zeckendorf-long-game-strategy.md`.

## Search log

- 2026-08-18: Queried the arXiv Atom API for `id_list=2508.20222`. HTTP 200 with
  `totalResults=1`; the entry resolved to `http://arxiv.org/abs/2508.20222v2`,
  title *The Ordered Zeckendorf Game*, six authors as recorded above, published
  2025-08-27, primary category `math.NT`. The API reported no `arxiv:doi` and no
  `arxiv:journal_ref`, so the arXiv-assigned DOI is used. The resolved entry is
  version 2; the DOI above is version-independent, and the problem candidate
  records the version it quotes.
- 2026-08-18: Issued `HEAD https://doi.org/10.48550/arXiv.2508.20222`, which
  returned HTTP 302 redirecting to `https://arxiv.org/abs/2508.20222`.

No literature search for a later resolution of Conjecture 1.7 was performed; the
open status recorded in the problem candidate is the status stated in this
arXiv version.

## Verified locator

- arXiv: https://arxiv.org/abs/2508.20222
- DOI: https://doi.org/10.48550/arXiv.2508.20222
