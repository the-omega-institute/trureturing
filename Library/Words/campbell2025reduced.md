---
bibkey: campbell2025reduced
authors: John M. Campbell, James Currie, Narad Rampersad
year: 2025
title: Reduced complexities for sequences over finite alphabets
doi: 10.48550/arXiv.2509.16034
claim: Section 3 leaves the odd-index recurrence and equation (11) for the reduced abelian complexity of the Thue-Morse word unproved.
strata_touched:
  - D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd
  - D5/S1/Words/Complexity/ThueMorseReducedAbelianEven
license: citation-only
triage: anchor
---

# Reduced complexities for sequences over finite alphabets

This note anchors only the odd-index equality in Section 3 (Conclusion),
page 15 of arXiv:2509.16034v1, for
`Problems/thue-morse-reduced-abelian-odd.md`. The caller-supplied reading,
2026-09-07, transcribes the source sentence as:

> Although it appears that rho^{ab,red}_t(2n+1) = rho^{ab,red}_t(n+1) for
> nonnegative integers n, the problem of determining a full recursion for
> rho^{ab,red}_t(n) seems to be challenging.

The caller reports that the odd equality is not proved anywhere in the paper.
The same paragraph leaves four further items. Two of them stay outside this
note: the sign of `rho(4n+2) - rho(4n)` when nonzero, and a recursion for
`rho(4n)`. Non-k-automaticity of sequence (10) also stays outside. Equation
(11) is now inside, and the next section records it.

## Equation (11)

Read on September 8, 2026 from the full-text rendering at
`https://arxiv.org/html/2509.16034v1`. The LaTeX source of the display, in the
Conclusion, is

    \left|\rho^{ab,red}_{t}(4n+2)-\rho^{ab,red}_{t}(4n)\right|
      = \begin{cases}0&\text{if $t_{n+1}=t_{3n+1}$},\\
                      1&\text{otherwise},\end{cases}

and the sentence carrying it reads "It appears that [(11)] holds, but it is
unclear how the sign of ...". The authors state a few lines later that they
leave proving equation (11) as an open problem.

Sequence (10) is printed as
`(2, 3, 3, 4, 3, 5, 4, 5, 3, 4, 5, 6, 4, 6, 5, 4, 3, 5, 4, ...)`.

### The index base, measured rather than assumed

The paper indexes both the complexity values and the Thue-Morse letters from
one; this repository indexes `thueMorse` from zero. The caller measured the
offset rather than inferring it, by computing the reduced Parikh vectors of
all factors directly and comparing seven candidate readings over `n = 1..299`:

| candidate reading, zero-indexed | disagreements |
| --- | --- |
| `t(n+1) = t(3n+1)` | 102 |
| `t(n) = t(3n)` | 0 |
| `t(n+1) = t(3n+2)` | 96 |
| four further shifts | 199 to 201 |

The same computation reproduces the printed sequence (10) term by term for
`n = 1..19` and satisfies the odd recurrence throughout, which is what pins
the complexity index to one as well. So in this repository's convention the
display reads `thueMorse n = thueMorse (3 * n)`.

The index `n = 0` sits outside the paper's range and outside the theorem:
there the difference is `R 2 - R 0 = 3 - 1 = 2`, so the hypothesis `0 < n` is
not cosmetic.

This comparison is an arithmetic reading over a bounded window together with a
human reading of the printed text. It is not a machine proof that the paper's
`rho` and this repository's `R` denote the same function.

On page 2, `red(w)` collapses every maximal constant run to one character.
Reduced abelian complexity counts equivalence classes of all length-`n`
factors: two factors are equivalent when their reduced words have equal
length and one is a rearrangement of the other. It does not count only
prefixes. Equality of reduced Parikh vectors expresses this equivalence,
since equal character counts also force equal reduced lengths.

The frozen module `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd` uses
zero-indexed binary digit parity for `thueMorse`, `List.destutter` for
`runCompress`, and `R` for the number of reduced Parikh vectors over all
natural starting positions. Its `reducedAbelianComplexity_odd` states
`R (2*n+1) = R (n+1)` for every natural `n`. The companion
`reducedAbelianComplexity_two_pow_add_one` states `R (2^k+1) = 3`; it is
supporting context, not a second problem anchor. The caller's comparison of
`R` with the paper's definition is a human reading, not a machine proof of
source-to-Lean equivalence.

**ASSUMED-UNVERIFIED:** the theory volume gives the printed venue as
*INTEGERS* 26 (2026), A34. Neither the caller nor this worker independently
verified that venue string. The front matter uses the verified 2025 arXiv
metadata and DOI.

## Search log

- Caller-supplied reading, 2026-09-07: queried
  `https://export.arxiv.org/api/query?id_list=2509.16034`, HTTP 200,
  `totalResults=1`. The entry is arXiv:2509.16034v1 with the title and authors
  above, published `2025-09-19T14:38:51Z`, primary category `math.CO`.
  No `arxiv:doi` or `arxiv:journal_ref` was reported. API response byte count
  was not supplied.
- Caller-supplied reading, 2026-09-07:
  `HEAD https://doi.org/10.48550/arXiv.2509.16034` returned HTTP 302 to
  `https://arxiv.org/abs/2509.16034`; no response byte count was supplied.
- Caller-supplied reading, 2026-09-07:
  `https://arxiv.org/pdf/2509.16034v1` returned HTTP 200, 309503 bytes,
  18 pages, SHA-256
  `b38c8326c8b7d8b0bea8b8f37cc368230f7d9b9c090070177b2b77cfba9a0cbe`.
  The caller located the definition on page 2 and the unproved equality in
  Section 3 on page 15, and compared the definition against Lean's `R`.
- Worker reading, 2026-09-07: read the local all-start factor definitions,
  public recurrence and corollary, and frozen-state receipt. The HTTP
  resources above were not fetched again; no venue lookup was performed.

No literature search for a later resolution of the conjecture was performed; the
open status recorded in the problem candidate is the status stated in this
arXiv version, not an assessment of the subsequent literature.

## Verified locator

- arXiv: https://arxiv.org/abs/2509.16034v1 (caller-supplied metadata).
- DOI: https://doi.org/10.48550/arXiv.2509.16034 (caller-supplied HTTP 302).
- PDF: https://arxiv.org/pdf/2509.16034v1 (definition, page 2; Section 3,
  page 15; caller-supplied HTTP 200).
