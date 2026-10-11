---
bibkey: fiore2026squaresideddice
authors: Evelyn Fiore, George D. Nasr, and Cooper Stone
year: 2026
title: "Dice Relabeling using Square-Sided Dice"
doi: null
url: https://arxiv.org/html/2606.20311v1
claim: "Definition 6.1 defines the full cyclotomic pairs; Conjecture 6.8 explicitly includes negativity at the midpoint when p is not two."
strata_touched:
  - D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation
license: CC-BY-4.0
triage: anchor
---

<!-- GID: D5/L/Factorization/fiore2026squaresideddice -->

# The square-sided-dice midpoint assertion

## Verified locator

Evelyn Fiore, George D. Nasr and Cooper Stone, *Dice Relabeling using
Square-Sided Dice*, arXiv:2606.20311v1, 18 June 2026, Definition 6.1,
Table 2, Lemma 6.6 and Conjecture 6.8. The primary HTML at https://arxiv.org/html/2606.20311v1
has 663149 bytes and SHA-256
`293426354df81fdb96ce3c34861f16a308fc299f215760752a07777f0b208ef3`.
The source is distributed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
The quotations and mathematical notation here are attributed to those authors;
the counterexample and its interpretation below are repository derivations.
No paper, experimental program or experimental data is redistributed here.

## Exact assertion and domain

Section 6 treats distinct primes p, q and r and exponents a,b,c,d in
{0,1,2}. Definition 6.1 gives

$$A_{abcd}(X)=X\Phi_p(X)^2\Phi_q(X)^2\Phi_{pq}(X)^a\Phi_{pr}(X)^b\Phi_{qr}(X)^c\Phi_{pqr}(X)^d,$$

$$B_{abcd}(X)=X\Phi_r(X)^2\Phi_{pq}(X)^a\Phi_{pr}(X)^b\Phi_{qr}(X)^c\Phi_{pqr}(X)^d.$$

The pair uses B with exponents 2-a,2-b,2-c,2-d. The complete Conjecture 6.8 is:

> In the remaining 33 pairs of the polynomials A_abcd and B_(2-a,2-b,2-c,2-d) (including the case where p != 2 for when a=b=c=d=1), one of the two polynomials will have a negative coefficient.

The midpoint is an explicitly included clause. The pairwise distinct odd
primes 3,5,11 satisfy it, including p != 2. They also satisfy p<q<r and
have r maximal, so conventions about ordering cannot exclude this instance.
The formal claim retains all factors and every natural coefficient index.
It is the midpoint universal assertion, not a full encoding of the
remaining exponent cases. Falsifying this expressly required instance
falsifies the source conjecture.

## Source boundaries

Table 2 duplicates (2,1,1,2); its printed count 33 does not justify an
invented remaining-case predicate. Lemma 6.6's assertion that sums of
odd-prime multiples are always even fails at 11=2*3+5. The lemma is not a
proof supplier. Its necessity claim for midpoint B is contradicted by the
complete nonnegative factorization at 3,5,11. No corrected classification
of all exponent tuples is asserted. Section 3's coefficient convention
allows zeros; nonnegative coefficients, rather than strictly positive
coefficients at all degrees, are the relevant condition.

## Literature boundary

The bounded source intake checked the latest arXiv version (v1), the exact
title, and the predecessor arXiv:2408.10331v2 / DOI
`10.54550/eca2025v5s2r9`. Source-specific public Problems and issue/PR
searches and private-inclusive D5/Library/Problems searches found no
matching resolution in that scope. Issue #11894 concerns the different
Conjecture 5.7 Q01 classification. Rate limits at OpenAlex and Semantic
Scholar and unavailable search endpoints limit the search. No exhaustive
priority, novelty or global absence assertion follows from these readings.
