---
slug: maity-krishna-2025-mutual-abelian-border-limits
bibkey: maitykrishna2025mutuallyabelian
doi: 10.1007/978-3-032-17801-5_6
url: https://arxiv.org/abs/2509.20773v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity.result
---

# Maity–Krishna's mutual abelian-border limit question

## Problem

Maity and Krishna, “Mutually Abelian-Bordered Binary Words”, arXiv:2509.20773v1,
Section 5 (Conclusion), question 1, p. 29, ask:

> “Do the limits $\lim_{n\to\infty} \mathcal{M}(n)/2^{2n}$ and $\lim_{n\to\infty} \overline{\mathcal{M}}(n)/2^{2n}$ exist?”

The counts concern ordered pairs of binary words of the same length. An internal
abelian border compares a nonempty proper suffix of the first word with a prefix
of the second; an external border compares a prefix of the first with a suffix
of the second. Abelian equivalence means equal counts of every letter.
The two border lengths may differ and the borders may overlap. The first count
requires both borders; the second requires neither.

## Motivation

The frozen declaration
`D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity.result` answers the
published question over the literal finite-word counts. The binary alphabet is
Bool, and words are the existing `BoundedRunSpace.Word` carrier `Fin n → Bool`.

## Gap

The published question requests existence of both normalized limits. The
preregistration is issue #13242. Its bounded literature inspection reports no
resolution in the inspected later sources; this does not assert worldwide
absence of a proof. The kernel-checked result provides the two existence
witnesses, with values 1 and 0.

## Route

Reverse the first word and interleave it with the complemented second word.
Equality of letter counts at border length r is equivalent to a zero of the
unit-step prefix height at time 2r. Odd times cannot have height zero.
A pair without an internal border therefore gives a zero-avoiding prefix.
The first sign and the oriented, shifted nonnegative walk encode that prefix
injectively. The two final bits are unrestricted.

The first-step bijection and Pascal induction count nonnegative walks. Writing
N(n) for the number of pairs without an internal border, the proof gives
$N(m+2) \le 4\binom{2m+2}{m+1}$. The frozen binomial estimate gives
$(\binom{2k}{k}/4^k)^2 \le 1/(2k+1)$, so N(n)/4^n tends to zero.
Swapping the words equates the internal and external exceptional counts.
The inequalities $4^n-\mathcal{M}(n) \le 2N(n)$ and
$\overline{\mathcal{M}}(n) \le N(n)$ then squeeze both densities.

## Falsifier

A binary ordered pair for which equality of suffix/prefix letter counts fails
to correspond to a zero at the specified even time would invalidate the route.
So would a failure of injectivity, the walk-count induction, or the uniform
exceptional-pair bound. Restricting the borders to nonoverlapping factors,
requiring their lengths to agree with each other, or omitting a binary letter
would change the source question.

## Evidence

The source definitions are Section 1, Definitions 1.1–1.2, p. 2; the counts
are introduced in Section 2, p. 3, and Section 3, p. 25. The
[literature note](../Library/Words/maitykrishna2025mutuallyabelian.md) provides
the DOI, stable versioned URL, verified locator and verbatim clauses.

`MutualAbelianBorderDensity.result : claim` proves the conjunction of the two
existential real-limit statements with no mathematical hypotheses. Its proof
term selects 1 for M and 0 for Mbar. These values are explicit proof witnesses;
the public statement is the paper's existence question. The natural-index
extension includes n=0 and does not alter the limits at infinity.

The following brute-force check enumerates all ordered binary word pairs and
counts those with no internal border. Equality of the number of 1s suffices
because both factors have the same length, so it also forces equality of the
number of 0s. For $1 \le n \le 10$, the computed values satisfy
$N(n)=4\binom{2n-2}{n-1}$:

| n | N(n): no internal border | $4\binom{2n-2}{n-1}$ |
| ---: | ---: | ---: |
| 1 | 4 | 4 |
| 2 | 8 | 8 |
| 3 | 24 | 24 |
| 4 | 80 | 80 |
| 5 | 280 | 280 |
| 6 | 1008 | 1008 |
| 7 | 3696 | 3696 |
| 8 | 13728 | 13728 |
| 9 | 51480 | 51480 |
| 10 | 194480 | 194480 |

Reproducible command (Python 3; exit 0):

```sh
python3 - <<'PY'
from itertools import product
from math import comb

for n in range(1, 11):
    words = list(product((0, 1), repeat=n))
    no_internal = 0
    for u in words:
        for v in words:
            if not any(sum(u[n-r:]) == sum(v[:r]) for r in range(1, n)):
                no_internal += 1
    predicted = 4 * comb(2*n-2, n-1)
    assert no_internal == predicted, (n, no_internal, predicted)
    print(n, no_internal, predicted)
PY
```

This finite computation does not certify the sharp count for all lengths;
that identity remains open in this delivery.

Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

Tier 1: an explicitly stated question in a published paper. Resolution: Proved.

### What the settlement shows

- **Proved in this module:** both binary densities converge. The proof supplies
  values 1 and 0. The decisive mechanism is the injection into surviving walks,
  followed by a central-binomial exceptional-density bound and symmetry.
- **Proved inside the result:** the exceptional-pair upper bound is uniform in
  length; the source permits overlapping borders and independent border lengths,
  and the proof retains both freedoms.
- **Proved in `D5/S3/StatisticalMechanics/RandomWalks/WalkCount.walk_count`:**
  the general reflection count permits every natural starting height and every
  walk length. It takes the existing walk family and its defining equation.
- **Computed:** kernel evaluation of the finite definitions gives M(3)=26 and
  Mbar(3)=10. The all-length sharp count and sharp density rates remain **open
  in this delivery**; the Lean proof only needs the upper bound.
- **Open:** extending the density result to three letters by a recurrence
  argument, or to larger alphabets by higher-dimensional return probabilities,
  requires additional estimates and a joint-event analysis. No nonbinary limit
  or independence statement is claimed here.
- **Open:** the source's question 2 (unequal lengths) and question 3 (nonbinary
  enumeration) are not settled by this binary, equal-length argument.
- **Source consequences:** question 1 receives an affirmative answer. The
  source's finite enumeration results do not assume an answer to question 1;
  the source introduces the limit expressions in its concluding question list.
  Their finite counting statements are retained, and questions 2 and 3 retain
  their original scope.

## ASSUMED-UNVERIFIED

The bounded literature search does not certify absence of other published or
unpublished resolutions. The all-length sharp count, convergence rates and
nonbinary extensions are not certified by this module. They are follow-up
questions rather than parts of the recorded settlement.
