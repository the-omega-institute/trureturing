---
bibkey: benfieldlippard2025pisanozeros
authors: Brennan Benfield, Oliver Lippard
year: 2025
title: "Connecting Zeros in Pisano Periods to Prime Factors of K-Fibonacci Numbers"
doi: null
url: https://arxiv.org/abs/2407.20048v2
claim: 'Conjecture 5.3. For an $(a,b)$-Fibonacci sequence, the range of $\omega_{(a,b)}(m)$ for $m>1$ is given by (i) $\{1\}$ if $(a,b) \in \{(0,1),(1,0),(-1,-1),(\pm2,-1)\}$, or if $m=2$ and $(a,b) \in \{(-1,0),(1,-1),(0,-1)\}$, (ii) $\{2\}$ if $m>2$ and $(a,b) \in \{(-1,0),(1,-1),(0,-1)\}$, (iii) $\{1,2,4\}$ if $b=1$ and $a\neq0$, (iv) $\{1,2\}$ if $b=-1$ and $a\not\in\{-2,-1,0,1,2\}$, (v) $\{0,1,2\}$ if $b \neq \pm1$ and $|a|-|b| = 1$, (vi) infinite in all other cases.'
strata_touched:
  - D5/S1/Recurrence/LucasEvenDescent
  - D5/S1/Recurrence/LucasCompanion
license: citation-only
triage: anchor
---

# Connecting Zeros in Pisano Periods to Prime Factors of K-Fibonacci Numbers

The paper studies the order of a modulus, defined in Section 1 as the number of zeros in one
Pisano period: "The number of zeros in a Pisano period is the order of `m`, denoted
`omega(m)`." For the ordinary Fibonacci sequence that count is classically 1, 2 or 4. The paper
proves several conjectures relating those counts to the prime factors of K-Fibonacci numbers,
and Section 4 extends the objects to `(a,b)`-Fibonacci sequences, defined there by `F_0 = 0`,
`F_1 = 1`, `F_n = a F_{n-1} + b F_{n-2}`.

Section 5, "Final Remarks", carries the conjecture quoted above on the range of the order as
the parameters vary. Section 5 also fixes the convention used for the degenerate moduli: "define
the order to be zero if the sequence is eventually periodic modulo `m` and this period contains
no multiples of `m`; this appears to occur if and only if `m` shares a common factor with either
`a` or `b`."

Status: clause (v) refuted by `(a,b) = (3,2)` at `m = 13` (this repository,
`D5/S3/Arith/PisanoOrderRangeRefutation.result`). The sequence modulo 13 runs
`0, 1, 3, 11, 0, 9, 1, 8, 0, 3, 9, 7` and then returns to `(0,1)`, so its period is 12 and it
carries three zeros; `b = 2` is not `±1` and `|3| - |2| = 1`, so the pair meets the hypothesis
as printed.

The defect is localised to the direction of the subtraction in clause (v). Finiteness of the
order in this region comes from the characteristic polynomial `x^2 - a x - b` having `±1` among
its roots: `b = a+1` gives roots `a+1` and `-1`, and `b = 1-a` gives roots `1` and `-a`. In
either case the sequence has a closed form whose vanishing is governed by a single multiplicative
order, so a period carries at most two zeros. In absolute values that family is `|a| - |b| = 1`
when `b < 0` and `|b| - |a| = 1` when `b > 0`; the printed clause keeps only the first shape.
The worked example the paper itself reports, "the order of the `(3,4)`-Fibonacci sequence modulo
`m` is always 0, 1, or 2 for `m < 20000`", satisfies `|b| - |a| = 1` and does not satisfy the
condition as printed. The counterexample is supplied by this repository, not by the cited paper,
and the rest of Conjecture 5.3 is untouched by it.

Adjacent: Conjecture 6.5 clause (v) of the same authors' arXiv:2404.08194 is refuted in this
repository by `a = 47`, `m = 15`; Conjecture 5.2 of Fiebig, Mbirika and Spilker, reference [7]
of the present paper, is proved in `D5/S1/Recurrence/LucasEvenDescent`.

## Verified locator

Preprint: https://arxiv.org/abs/2407.20048v2, version 2 of 30 January 2025. The conjecture is
Conjecture 5.3 of Section 5 in the LaTeX source `fiborder.tex`, lines 729-741; the definition of
the sequences is in Section 4 and the definition of the order is in Section 1. No DOI is
declared for this note, so none is bound here.

Source boundary: the preprint was read; no journal version was compared line by line, and
citation indices were not exhaustively reachable.
