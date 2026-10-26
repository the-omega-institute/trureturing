---
bibkey: jaffe2026denominators
authors: Grace Natalie Jaffe
year: 2026
title: "Denominators in the Farey Sequence, the Stern Sequence, and the Frobenius Problem with Relatively Prime Multipliers"
doi: null
url: https://arxiv.org/abs/2610.17267v1
claim: "Conjecture 7.3 bounds g(a,c(a,b))/g(a,b) by 5 for every coprime pair of integers a,b at least 3, where c(a,b) is the least integer greater than b and coprime to a, and g uses primitive nonnegative coefficients."
strata_touched:
  - D5/S3/ArithUnits/JaffeSuccessorRatioRefutation
license: CC-BY-4.0
triage: anchor
---

# Primitive nonnegative representations and the successor-ratio conjecture

## Verified locator

The [versioned source](https://arxiv.org/abs/2610.17267v1) is arXiv:2610.17267v1.
Its [primary HTML](https://arxiv.org/html/2610.17267v1), Section 3, defines
\[
R(a,b)=\{ax+by:x,y\in\mathbb Z_{\geq0},\ \gcd(x,y)=1\}.
\]
The quantity \(g(a,b)\) is the greatest integer in
\(\mathbb Z\setminus R(a,b)\), with infinity when there is no greatest
missing integer. The axes are included: the coefficients are nonnegative,
as stated in Section 3. The introduction's positive-coefficient wording
does not replace this definition.

Section 7, Conjecture 7.3, states:

> For all a,b >= 3 relatively prime and for c(a,b) the minimum integer satisfying both c(a,b)>b and gcd(c(a,b),a)=1, we have g(a,c(a,b))/g(a,b) <= 5.

There is no global \(a<b\) convention. The local ordered hypotheses in
Section 2 and the ordered dataset following Conjecture 7.3 are separate
conditions. Section 7 also considers fixed \(b=3\) and larger \(a\).
Symmetry of \(g\) does not make its asymmetric successor operation
invariant under exchange of the two arguments.

The retained primary HTML has 451,273 bytes and SHA-256
`3ea624b4ac5a553f9b0b348a7f9079d096f20871ced150f1a593b1022cc66f9f`.
The retained text has 47,585 bytes and SHA-256
`71e5ef50ec26c31589d69dee838a778f6ccdad99eb90dc09356505ed526d95ac`.
The HTML identifies the source license as CC BY 4.0. No external proof code
is transplanted.

## Earlier and related statements

The same author's *Topics in analytic number theory*, University of Illinois
Urbana-Champaign dissertation, 2023, states this same assertion as
**Conjecture 8.3**, printed page 43 / PDF page 51. The institutional record is
https://www.ideals.illinois.edu/items/127306 and the persistent handle is
https://hdl.handle.net/2142/120085. The checked PDF has 1,895,118 bytes and
SHA-256 `2f668879c4ec48a6b292a79bb35cbf617ad3c1d2a08ebd7d2c038fa512e36259`.
Its relevant conjecture, numerical discussion and appendix do not supply a
whole proof or refutation. The thesis and paper name one mathematical target.

Shunpei Shimizu's *A factor-four lower bound for the Frobenius problem with
relatively prime multipliers (Jaffe's Conjecture 7.2)*, draft v0.1.1,
DOI https://doi.org/10.5281/zenodo.23480212, concerns the different
factor-four lower bound. The inspected main manuscript does not settle the
successor-ratio Conjecture 7.3. It is not used as a theorem here.

## Refutation and prior ingredients

The formal source is
`D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.lean`. Its `Represented`
predicate uses nonnegative integer coefficients and their actual gcd;
`sourceG` selects the greatest missing integer and returns infinity when
one does not exist. `fullClaim` quantifies over all coprime integers
\(a,b\geq3\), with neither coordinate order assumed. The designated theorem
`result` has the literal type `Not fullClaim`.

The counterexample is
\[
a=87841397512641630,\qquad b=7,\qquad c(a,7)=49.
\]
Every integer from 8 through 48 shares a factor with \(a\), whereas
\(\gcd(a,7)=\gcd(a,49)=1\). Scaling a missing integer for \((a,7)\) by 7
gives a missing integer for \((a,49)\): any purported primitive
representation would force the first coefficient to be divisible by 7,
and division would preserve primitive coefficients. Consequently the actual
maxima satisfy \(g(a,49)\geq7g(a,7)>0\), so their well-defined quotient
exceeds 5.

Finiteness is proved, rather than assumed. If \(H(n)\) counts all
nonnegative solutions and \(P(n)\) the primitive ones, a gcd partition and
Möbius inversion give
\[
 ABP(n)\geq\varphi(n)-AB\,\tau(n),
 \qquad n\tau(n)^2\leq16^7\varphi(n)^2,
\]
where \(\tau(n)\) is the number of positive divisors of \(n\). Thus every
\(n>16^7(AB)^2\) is represented. The missing integer 1 and this universal
tail give a positive greatest missing integer in \(\mathbb Z\).
The maxima themselves are not evaluated or replaced by prefix maxima.

The source's Theorem 4.3 already supplies the finiteness ingredient in
ordinary mathematics, and Theorem 7.1 supplies the scaling ingredient.
Their mathematical content is attributed to the source. The Lean proof
checks these ingredients using finite counting, divisor factorization and
coprimality; it does not assume the paper's theorems as axioms. The coarse
divisor-count cutoff is sufficient for the comparison and is not an
optimal bound.

## Qualification boundary

[Registration #20244](https://github.com/the-omega-institute/trureturing/issues/20244)
anchors the whole Conjecture 7.3. The bounded qualification checked the
versioned source, the relevant thesis passages, the related 7.2 manuscript,
and arXiv, OpenAlex, Crossref and targeted web results. No inspected text
gave a whole answer to this exact target. Citation indexing was incomplete:
the checked 7.2 manuscript cites the source although its citation-index
query returned zero records. Unindexed work, alternate terminology and
unvisited sources remain outside the checked scope. No global priority or
exhaustive absence claim follows.

The prior bounded repository, pinned Mathlib and third-party Lean searches
identified Möbius inversion, totient factorization and integer extrema APIs,
but no exact primitive-tail or whole successor-ratio result. Ordinary
`FrobeniusNumber` APIs omit coefficient coprimality and do not close this
gap. The pinned Mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679` with Lean 4.35.0. This is one
unfrozen candidate for one target; independent mirror review, freezing,
integration and accepted credit are separate obligations. The ordered
variant with \(a<b\) remains unresolved here.
