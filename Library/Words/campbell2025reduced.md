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

The front matter retains the arXiv:2509.16034v1 identity, dated September 19,
2025. The journal publication is John M. Campbell, James D. Currie and Narad
Rampersad, *Reduced Complexities for Sequences over Finite Alphabets*,
*INTEGERS* **26** (2026), A34, published February 20, 2026, with printed DOI
[10.5281/zenodo.18714474](https://doi.org/10.5281/zenodo.18714474).
The [journal PDF](https://math.colgate.edu/~integers/aa34/aa34.pdf) gives the
venue, authors, date and DOI on its first page; Rampersad's publication list
links that same PDF. This is a separate journal publication, not an arXiv v2.

This note anchors the odd recurrence and equation (11) through their existing
dossiers and records below a further implication of the recurrence ingredients.
Section 3 (Conclusion), printed page 14 of the journal version and page 15 of
arXiv:2509.16034v1, proposes the odd recurrence:

> Although it appears that rho^{ab,red}_t(2n+1) = rho^{ab,red}_t(n+1) for
> nonnegative integers n, the problem of determining a full recursion for
> rho^{ab,red}_t(n) seems to be challenging.

The paper leaves this equality unproved. Its final explicit open-question
sentence, on journal page 14, is:

> It also appears that the integer sequence in (10) is not k-automatic, and we leave it as an open problem to prove this.

Sequence (10), on journal page 13, is the full natural-valued reduced abelian
complexity at positive factor lengths. The source's open-question wording is
distinct from the mathematical consequence documented below.

## Equation (11)

Equation (11) appears in the same Conclusion. Its display in the
[arXiv v1 rendering](https://arxiv.org/html/2509.16034v1) is

    \left|\rho^{ab,red}_{t}(4n+2)-\rho^{ab,red}_{t}(4n)\right|
      = \begin{cases}0&\text{if $t_{n+1}=t_{3n+1}$},\\
                      1&\text{otherwise},\end{cases}

and the sentence carrying it reads "It appears that [(11)] holds, but it is
unclear how the sign of ...". The authors state a few lines later that they
leave proving equation (11) as an open problem.

Sequence (10) is printed as
`(2, 3, 3, 4, 3, 5, 4, 5, 3, 4, 5, 6, 4, 6, 5, 4, 3, 5, 4, ...)`.

### Letter indices, factor lengths and edge counts

The paper defines its first Thue-Morse letter at index one (journal page 3);
this repository indexes `thueMorse` from zero. Thus the paper's letter at
`n+1` is `thueMorse n`, and its letter at `3n+1` is `thueMorse (3*n)`.
Factor lengths do not shift: the paper's `rho(n)` corresponds to `R n`.
Sequence (10) starts at length one, while both definitions also allow length
zero. A recorded direct comparison of reduced Parikh vectors over
`n = 1..299` corroborates the letter-index translation:

| candidate reading, zero-indexed | disagreements |
| --- | --- |
| `t(n+1) = t(3n+1)` | 102 |
| `t(n) = t(3n)` | 0 |
| `t(n+1) = t(3n+2)` | 96 |
| four further shifts | 199 to 201 |

The same bounded computation reproduces sequence (10) for lengths `1..19`
and satisfies the odd recurrence throughout the comparison window. These
checks support the reading but do not establish an unbounded identity.

The equation-(11) theorem requires `0 < n`: at `n = 0` the difference is
`R 2 - R 0 = 3 - 1 = 2`, so this hypothesis is not cosmetic.

On journal pages 2–3, `red(w)` collapses every maximal constant run to one
character.
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
supporting context, not a second problem anchor. The source-to-Lean
correspondence is a reading of the definitions, not a machine-checked
equivalence between the paper's text and Lean.

The extrema use a different argument: `minAlternations n` and
`maxAlternations n` count changes across **n edges**, hence in factors of
length `n+1`. They correspond to the paper's length-indexed extrema
`m_(n+1)` and `M_(n+1)`.

## Consequence for sequence (10)

The recurrence mechanism is due to the paper's Theorem 1 and Lemmas 2–3.
The frozen module `ThueMorseReducedAbelianEven` contains the kernel-checked
ingredients `extrema_bounds`, `extrema_even`, `extrema_odd` and
`complexity_weighted`. In the repository's edge convention, put
`m(n) = minAlternations n`, `M(n) = maxAlternations n` and
`w(n) = M(n) - m(n)`. The bounds `m(n) <= M(n) <= n` justify the natural-number
subtractions in the even and odd recurrences. Applying those recurrences
twice gives, for every `n >= 0`,

    m(4n+1) = 2n + m(n),    M(4n+1) = 2n + 1 + M(n),
    w(4n+1) = w(n) + 1,    w(0) = 0.

The all-start weighted interval formula sums over run counts from `m(n)+1`
through `M(n)+1`, with weight `1 + (r mod 2)` at run count `r`. Every weight is at
least one, so

    R(n+1) >= M(n) - m(n) + 1 = w(n) + 1.

Set `a_0 = 0` and `a_(j+1) = 4a_j + 1`. Induction gives `w(a_j) = j`,
and therefore `R(a_j+1) >= j+1` for every `j >= 0`. These are positive
factor lengths, so `R` is unbounded on positive lengths. A finite automaton
with a natural-valued output map has only finitely many output values and
hence a bounded range. It cannot produce this sequence in any integer base
`k >= 2`. Thus the full sequence (10) is non-k-automatic for every such base.

This is unboundedness, not convergence of `R(n)` to infinity: the existing
`R(2^k+1) = 3` is compatible with the argument. The implication here is
exposition from existing results; no separately kernel-checked
nonautomaticity endpoint or typed resolution claim is supplied. It does not
determine the nonzero sign in equation (11), a recursion for `R(4n)`, or a
full recursion for `R(n)`.

## Literature scope

Targeted literature and third-party Lean searches through September 14, 2026
found no direct later resolution of this nonautomaticity question in the
searched scope. This is not a worldwide absence or priority certification.
*Reflection on the Reflection Complexity*, arXiv:2511.12358v1 and its
May 18, 2026 journal version, DOI
[10.1007/s00224-026-10278-7](https://doi.org/10.1007/s00224-026-10278-7),
concerns reversal/reflection equivalence and eventual periodicity; it does
not settle this reduced-abelian question. The search conclusion does not
establish first-publication priority for the odd recurrence or equation (11).

## Verified locator

- arXiv: https://arxiv.org/abs/2509.16034v1 (September 19, 2025).
- arXiv DOI: https://doi.org/10.48550/arXiv.2509.16034.
- PDF: https://arxiv.org/pdf/2509.16034v1 (definition, page 2; Section 3,
  page 15).
- Journal PDF: https://math.colgate.edu/~integers/aa34/aa34.pdf (publication
  metadata and DOI, page 1; definitions, pages 2–3; sequence (10), page 13;
  Section 3 and final open-question sentence, page 14). Verified capture
  SHA-256: `a5d9c6ee3c05e0032806910a454f442e5ae13ce673bea384ff2abf7371db4d31`.
- Journal DOI: https://doi.org/10.5281/zenodo.18714474.
- Author's publication list: https://nrampers.faculty.uwinnipeg.ca/publications.html
  (journal entry linking the same PDF).
