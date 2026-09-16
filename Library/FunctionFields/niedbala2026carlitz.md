---
bibkey: niedbala2026carlitz
authors: David Niedbala Giraudin
year: 2026
title: "A counterexample to a conjecture of Thakur on Carlitz-Wieferich primes"
doi: 10.48550/arXiv.2607.15305
url: https://arxiv.org/abs/2607.15305
claim: "Version 2, Conjecture 4.2: over F_(19^3), gcd(T^(q^5)-T,M_(5,q)) equals mu(T^q-T), with mu=X^5+5X^3+3X^2-4X-9."
strata_touched:
  - D5/S3/Arith/FunctionField/CarlitzFiveOrbit
license: CC-BY-4.0
triage: anchor
---

# Carlitz degree-five exactness

The relevant primary version is arXiv:2607.15305v2, dated 22 July 2026:
https://arxiv.org/html/2607.15305v2 . The abstract and version comment explicitly
say that the former exactness theorem was corrected to a conjecture. It is
not valid to quote the superseded version-one exactness label as a proof.

Theorem 1.1 supplies an explicit irreducible Carlitz-Wieferich quintic over
F_(19^3). Theorem 4.1 proves that its 6859 translates have product
mu(T^q-T) and that this product divides the gcd. Those results are established
inputs of the source, not the new target. Conjecture 4.2 asks whether any
additional factor exists. The discussion isolates a possible difference
eta=theta^q-theta of degree fifteen over F19; the low-degree difference
case was already accounted for.

The companion *Effective determination of Carlitz-Wieferich primes of given
degree* is listed as in preparation in version 2. Searches for the exact
arXiv identifier, exactness conjecture number, companion title, and combined
Carlitz-Wieferich completeness terms did not locate a later published proof
in the checked sources. This is a bounded literature check, not an assertion
of worldwide priority or author/editor acceptance.

The new certificate uses the literal nested residual from equation (2),
its five conjugates, and the literal mu from Conjecture 4.2. It proves that
all solutions of the resulting orbit equations have quintic difference.
The corresponding ordinary proof concludes exactness and also handles all
constant fields F_(19^s). The original counterexample to Thakur's suggestion
is not counted again.

Earlier primary sources for the criterion are:

- D. S. Thakur, *Fermat versus Wilson congruences, arithmetic derivatives and
  zeta values*, Finite Fields and Their Applications 32 (2015), 192-206.
- A. S. Bamunoba and J. Bergstrom, *A search for c-Wieferich primes*,
  International Journal of Number Theory 17 (2021), 1599-1616,
  https://arxiv.org/abs/2011.11727 .

Function-field Carlitz-Wieferich primes are distinct from integer
Wall-Sun-Sun primes. The characteristic-nineteen elimination certificate
has no asserted implication of integer WSS existence.

## Unified owner and the all-characteristic continuation

All CF1-CF5 proofs now live under the existing owner
`Problems/wall-sun-sun-golden-unit-lift.md`, followed by CX1-CX6. The former
separate Carlitz problem file was removed only after its complete mathematics
was retained there. This Library note remains a source record, not a second
open-problem entry. The existing CarlitzFiveOrbit Lean/Scribe pair is unchanged.

The source's Proposition 5.2 reports finite prime-field computations, with
its degree-five row covering p=3,7,11,13,17,19,23,29,31,37. It does not give
the uniform all-odd-characteristic classification developed in CX. The new
integer five-orbit certificate restricts odd characteristic to5,19,263 and
519555805809266011. Additional exact certificates and constructions give
extension classes s=3 modulo5 for263 and s=4 modulo5 for the large prime.
Together with CF this excludes degree-five nonconforming examples over every
odd prime field. These new mathematical conclusions are not attributed to
the source author, and do not answer the source's prime-field question in
higher degrees.

The companion paper remains listed as in preparation in the checked v2.
Exact searches for Carlitz-Wieferich together with263, the large characteristic,
the companion title and degree-five completeness did not locate the new
families in the checked primary sources. The known characteristic19 result
and its already delivered completeness proof are not counted again. Neither
absence from indexed search nor an unpublished companion's unknown contents
establishes worldwide priority. External acceptance remains unconfirmed.
