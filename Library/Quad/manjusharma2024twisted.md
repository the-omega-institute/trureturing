---
bibkey: manjusharma2024twisted
authors: Praveen Manju and Rajendra Kumar Sharma
year: 2024
title: Twisted Derivations in Algebraic Number Fields
doi: null
url: https://arxiv.org/abs/2412.03507v2
claim: "Conjectures 4.4 and 5.2 give printed adjugate innerness and outer-class criteria with denominator p^e on prime-power cyclotomic integer rings."
strata_touched:
  - D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour
  - D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo
license: arXiv-nonexclusive-distrib-1.0
triage: anchor
---

# Twisted derivations on prime-power cyclotomic integer rings

## Verified locator

Primary version: https://arxiv.org/abs/2412.03507v2.
Conjecture 4.4: https://arxiv.org/html/2412.03507v2#S4.Thmtheorem4.
The authors' TeX source, `Twisted_derivations_in_algebraic_number_fields.tex`,
is available from https://arxiv.org/src/2412.03507v2.
Definition 2.1 is at source lines 135–137, the Section 4 domain and matrix
construction at lines 470–472, the Section 4.2 domain at 1276–1277,
Conjecture 4.3 at 1281–1283 and Conjecture 4.4 at 1287–1289.
The introduction's primitive-root and n-at-least-three domain is at line 120.
The TeX resolves the inherited reference to Conjecture 4.3; the HTML
cross-reference display is not used to infer its target.

## Source scope

The source takes K=Q(zeta), with zeta a primitive n-th root, n at least three,
and O_K=Z[zeta]. The twists are distinct nonzero integer-algebra endomorphisms
with sigma(zeta)=zeta^u and tau(zeta)=zeta^v, where u,v are distinct units
represented below n. Section 4.2 takes n=p^k for any rational prime p and
natural k unequal to one. The odd-prime restriction in Section 4.1 does not
apply to Section 4.2.

Definition 2.1 requires D to be integer-linear and to satisfy
D(xy)=D(x)tau(y)+sigma(x)D(y) for all x,y. Innerness requires an integral
gamma with D(x)=gamma*tau(x)-sigma(x)*gamma for every x.

For v-u=p^e*m with m positive and prime to p, Conjecture 4.3 asserts
that the multiplication matrix A of tau(zeta)-sigma(zeta), in the ordered
integral power basis, has determinant plus or minus p^(p^e). This is a
conclusion, not a hypothesis that an integral solution of D(zeta) exists.
C is the coordinate column of D(zeta).

Conjecture 4.4 states that D is inner if and only if
(1/p^e)Adj(A)C is integral. It also states separately that divisibility of
all C coordinates by p^e suffices, and that divisibility by p suffices.
The denominator p^e is preserved literally. Version 1 independently prints
the same denominator and both additional assertions:
https://arxiv.org/html/2412.03507v1.

## Counterexample and boundary

In the actual fourth cyclotomic integer ring take the ordered basis (1,z),
where z^2=-1, sigma the identity, tau conjugation, and D(a+bz)=b.
Here p=2, k=2, u=1, v=3, e=1 and m=1. The full twisted product law holds.
The actual matrix is [[0,2],[-2,0]], C=(1,0), det(A)=4 and
(1/2)Adj(A)C=(0,1). Innerness would force 1=2b for an integer b.
Table 3 prints the opposite matrix sign for this case. Section 4 defines A
by multiplication by tau(zeta)-sigma(zeta), which gives the matrix above;
the table and defining formula are inconsistent at that sign.
This negates the whole printed universal claim through its iff. It does not
separately negate the two sufficient assertions or a repaired statement.
The quadratic classification is prior literature; the formal delivery
claims the application to this full printed named problem, not a new
classification of quadratic derivations. A bounded literature screen is
not an exhaustive novelty certificate.

## Conjecture 5.2

Conjecture 5.2 is at TeX lines 2240–2242, Section 5.2:
https://arxiv.org/html/2412.03507v2#S5.SS2.
The primary TeX SHA-256 is
`61eac8e439f53269a30a61579d0c822058c9752410a3f65fb5c4e67309b9ce18`.
Its complete assertion is that D is outer if and only if
(1/p^e)Adj(A)C is not integral, and that Inn is a strict submodule of Der
for every admissible pair, equivalently there is a nonzero outer class.
All prime-power, field, integer-ring, basis, twist and factorization
hypotheses are those described above. The determinant conclusion of
Conjecture 4.3 is not assumed.

Definition 2.1 and the Remark at TeX lines 156–158 identify a non-inner
representative with a nonzero class in the actual quotient Der/Inn.
For a reversed exponent pair, the positive source factorization is used
after exchanging the twists. Commutativity preserves the twisted law,
negating the integral multiplier preserves the inner submodule, and
A changes to -A. The classical adjugate identity
Adj(-A)=(-1)^(N-1)Adj(A) preserves the integrality test. Thus the two-order
formulation includes every distinct pair without changing the denominator.

The same actual fourth-root derivation described above is non-inner,
so its quotient class is nonzero, while the printed vector is integral.
This contradicts the criterion in the complete conjunction. It does not
separately refute the universal strict inclusion or a corrected criterion.
The [Conjecture 5.2 dossier](../../Problems/manju-sharma-2024-conjecture-5-2-refutation.md)
gives the full source-to-statement correspondence and the surviving boundaries.

## License

The versioned arXiv abstract links to
http://arxiv.org/licenses/nonexclusive-distrib/1.0/ as its article license.
This is the arXiv nonexclusive distribution license, not a Creative Commons
license. Copyright remains with the authors. This note supplies locators,
mathematical paraphrase and the counterexample; it does not redistribute
the article or its source archive.
