---
slug: crux-problem-2623-refutation
bibkey: zejnulahiarslanagic2001problem2623
doi: null
url: https://cms.math.ca/wp-content/uploads/crux-pdfs/CRUXv27n2.pdf
triage: theorem
motivation_gids:
  - D5/S0/Certificates/CruxProblem2623Refutation
---

# Refutation of Crux Problem 2623

## Problem

Zejnulahi and Arslanagic, *Problem 2623*, Crux Mathematicorum with
Mathematical Mayhem 27, no. 2 (2001), displayed page 139, define positive
cyclic variables by `x_(n+r) = x_r` and

`S_k = sum_(j=1)^n (sum_(i=0)^k x_(j+i)) / (sum_(i=0)^k x_(j+i+1))`.

They ask verbatim:

> Prove or disprove that S_k >= S_(k+1).

The formal claim quantifies over every `n >= 2`, every positive real-valued
cyclic function on `ZMod n`, and every interior index `k` with `k+2 <= n`.
It asserts `S_(k+1) <= S_k`.

## Motivation

The published question asks for either a proof or a disproof of a universal
monotonicity assertion. A positive four-cycle supplies an exact rational
counterexample at an interior index, so the endpoint convention does not
affect the refutation.

## Gap

Preregistration issue #8427 records the printed statement, its full
quantifiers, the first-tier journal-problem classification, and the proposed
counterexample before the Lean probe. Crux volume 28, no. 4, printed page 252
states that no solutions had been received and that the problem remained
open. The cumulative unsolved table in volume 36, no. 8, printed page 547
lists Problem 2623. Repository, in-flight, open-pull-request, arXiv, OpenAlex,
Crossref, and GitHub-code searches found no matching formalization or
published resolution in the checked scope. These are bounded surfaces; no
priority claim is made.

## Route

Take `n=4`, `k=1`, and the positive cyclic tuple `(1,2,1,2)`. The four terms
of `S_1` are all 1, so `S_1=4`. The four terms of `S_2` are
`4/5, 5/4, 4/5, 5/4`, so `S_2=41/10`. Hence `S_1 < S_2`, contradicting the
proposed inequality at an interior index.

## Falsifier

A proof of the literal interior-index claim would specialize at `n=4`,
`k=1`, and `(1,2,1,2)` to `41/10 <= 4`. The kernel-checked rational
calculation proves the opposite inequality, so such a proof would contradict
`D5/S0/Certificates/CruxProblem2623Refutation.result`.

## Evidence

- Lean module: `D5/S0/Certificates/CruxProblem2623Refutation.lean`.
- Main theorem: `result : not claim`, with exactly the std3 axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- The proof expands two four-term sums with inner ranges of lengths two and
  three, decides the closed `ZMod 4` indices in the kernel, and closes exact
  rational arithmetic without `native_decide` or numerical approximation.
- The source PDF has SHA-256
  `c2ce15e455786b1bac7e8ce360ebe4e106970b1efb0e290df6758821823a8e70`.

## Triage

`theorem`. The certified instance refutes the published universal
monotonicity assertion. The theorem proof shape is `bind-only`, the admission
basis is `open-problem-resolution`, and the utility basis is the typed
`refutes` edge from `result` to `claim`. No corrected monotonicity statement
is asserted.

## ASSUMED-UNVERIFIED

Whether a solution or refutation was published after the 2010 cumulative
table was not exhaustively verified. Several post-2010 CMS issue pages timed
out, the volume 45 index returned HTTP 503, and a later OpenAlex author query
was rate-limited. Exhaustive publication coverage and priority are not
claimed.
