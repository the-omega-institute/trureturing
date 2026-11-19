---
slug: manju-sharma-2024-conjecture-4-4-refutation
bibkey: manjusharma2024twisted
doi: null
url: https://arxiv.org/abs/2412.03507v2
triage: theorem
motivation_gids:
  - D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.result
---

# Manju–Sharma's printed Conjecture 4.4

## Problem

Praveen Manju and Rajendra Kumar Sharma, *Twisted Derivations in Algebraic
Number Fields*, arXiv:2412.03507v2, Section 4.2, Conjecture 4.4:
https://arxiv.org/html/2412.03507v2#S4.Thmtheorem4.
The primary TeX member is `Twisted_derivations_in_algebraic_number_fields.tex`
at https://arxiv.org/src/2412.03507v2. Its reference in Conjecture 4.4
explicitly names Conjecture 4.3. The following is a mathematical paraphrase
of the full assertion and its inherited domains, rather than a corrected criterion.

The introduction at TeX line 120 takes a primitive n-th root zeta with n at
least three. Section 4, lines 470–472, takes K=Q(zeta) and its actual ring of
integers O=Z[zeta], with two distinct nonzero integer-algebra endomorphisms
sigma and tau. Write sigma(zeta)=zeta^u and tau(zeta)=zeta^v, where u,v are
distinct natural representatives below n and each is coprime to n.
Section 4.2, lines 1276–1277, takes n=p^k for any rational prime p and
natural k unequal to one. The odd-prime restriction of Section 4.1 is absent.

Definition 2.1, lines 135–137, requires D:O→O to be integer-linear and to
satisfy, for every x,y in O,

$$D(xy)=D(x)\tau(y)+\sigma(x)D(y).$$

Innerness means that there exists gamma in O such that, for every x in O,

$$D(x)=\gamma\tau(x)-\sigma(x)\gamma.$$

Put N=p^(k-1)(p-1). Use the ordered integral power basis
(1,zeta,…,zeta^(N-1)). The matrix A is defined by

$$\left(\sum_{j=0}^{N-1}b_j\zeta^j\right)(\tau-\sigma)(\zeta)
 =\sum_{i=0}^{N-1}\left(\sum_{j=0}^{N-1}a_{ij}b_j\right)\zeta^i,
 \qquad A=(a_{ij}).$$

Thus A is the actual integer matrix of multiplication by
tau(zeta)-sigma(zeta), with column j giving the image of zeta^j.
C=(c_i) is the actual coordinate column determined by D(zeta)=sum_i c_i zeta^i.
Conjecture 4.3, lines 1281–1283, further writes v-u=p^e m, with e a
nonnegative integer, m a positive integer and p not dividing m. Positivity
requires v>u. Its conclusion det(A)=±p^(p^e) is an assertion, not a
hypothesis that an integral solution of AX=C already exists.

Under these hypotheses, Conjecture 4.4, lines 1287–1289, asserts the
following three statements together, universally over all the objects above:

$$\begin{aligned}
 D\text{ is inner}&\ \Longleftrightarrow\ p^{-e}\operatorname{Adj}(A)C\in\mathbb Z^N,\\
 (\forall i<N,\ p^e\mid c_i)&\ \Longrightarrow\ D\text{ is inner},\\
 (\forall i<N,\ p\mid c_i)&\ \Longrightarrow\ D\text{ is inner}.
\end{aligned}$$

Adj is the classical adjugate. The denominator is literally p^e; it is not
replaced by det(A) or p^(p^e). Version 1 independently prints this denominator
and both sufficient assertions: https://arxiv.org/html/2412.03507v1.

| Source clause | Lean counterpart |
| --- | --- |
| Every prime p, k≠1, n=p^k≥3 | Initial natural binders and hypotheses of `claim`; k=0 is excluded by n≥3. |
| Rational cyclotomic field and primitive zeta | `K`, `Field`, `NumberField`, `IsCyclotomicExtension`, `NeZero`, and `hζ : IsPrimitiveRoot ζ (p^k)`. |
| Actual integer ring and ordered integral powers | `RingOfIntegers K`, `z := hζ.toInteger`, and every `PowerBasis` with `gen=z` and `dim=N`; `basis_eq_pow` supplies the ordering. |
| Distinct nonzero twists and their root images | Integer-algebra endomorphisms with `σ≠τ`, bounds and coprimality of u,v, and the two root-image equations. Unital maps of this nontrivial ring are nonzero. |
| Nonnegative e, positive m, p not dividing m | Natural e,m with `0<m`, `¬p∣m`, and `v=u+p^e*m`. |
| Integer linearity and all-input twisted law | `D : O →ₗ[ℤ] O` and the hypothesis `∀ x y, ...`. |
| Integral inner witness | `IsInner` quantifies gamma in O and the equation over every x in O. |
| Defined matrix and defined column | `Algebra.leftMulMatrix pb.basis (τ z-σ z)` and `pb.basis.repr (D z)`; neither is an independent free matrix/vector. |
| Complete iff and both sufficient assertions | The three conjuncts of `claim`, with `PrintedIntegralTest` using rational inversion of p^e and an integer-vector witness. |
| Refutation of the full universal conjunction | The unique authored public theorem `result : ¬ claim`. |

## Motivation

The claim seeks an integral innerness criterion from the generator value of
a twisted derivation. A faithful counterexample must keep the actual
cyclotomic integer ring, its ordered power basis, its two endomorphisms and
the full product law. A freely chosen matrix or a merely rational inner
generator would not answer the integral question.

## Gap

The printed denominator can make the adjugate column integral even when the
unique rational solution of AX=C is not integral. In the fourth cyclotomic
case det(A)=4, while the printed denominator is 2. Table 3 gives the opposite
matrix sign for this case, inconsistent with the defining multiplication
operator in Section 4. The definition by tau(zeta)-sigma(zeta) fixes the
matrix used here; the argument does not silently adopt the table's sign.

## Route

Take the actual O4=`RingOfIntegers (CyclotomicField 4 Rat)`. Its primitive
integral root z satisfies z²=-1. The existing integral-power-basis theorem
gives dimension two, and reindexing gives exactly (1,z).
`Zsqrtd.lift`, its nonsquare injectivity result and reconstruction in that
actual basis give a proved integer-algebra equivalence GaussianInt≃O4
carrying the Gaussian generator to z. This establishes multiplication and
coordinates on the actual ring; no Gaussian identification is assumed.

Transport conjugation to obtain tau, set sigma to the identity, and transport
the imaginary-coordinate map to obtain D(a+bz)=b. For Gaussian coordinates
x=a+bz and y=c+dz, D(xy)=ad+bc, while
b(c-dz)+(a+bz)d=bc+ad. This all-input identity transports to O4, so D
satisfies the full twisted Leibniz law. Moreover D(z)=1 and tau(z)=-z=z³.
The two twists are distinct. Choose p=2,k=2,u=1,v=3,e=1,m=1; all prime,
unit, dimension, ordering and factorization hypotheses hold.

## Falsifier

Multiplication by tau(z)-z=-2z sends 1 to -2z and z to 2. Therefore

$$A=\begin{pmatrix}0&2\\-2&0\end{pmatrix},\qquad
C=\begin{pmatrix}1\\0\end{pmatrix},\qquad
\operatorname{Adj}(A)=\begin{pmatrix}0&-2\\2&0\end{pmatrix},\qquad
\tfrac12\operatorname{Adj}(A)C=\begin{pmatrix}0\\1\end{pmatrix}.$$

The printed integrality test holds. If an integral gamma=a+bz made D inner,
evaluation at z would give

$$1=\gamma(-z)-z\gamma=2b-2az.$$

The real coordinate forces 1=2b with b an integer, a contradiction. Thus
the iff fails in its test-to-inner direction, negating the entire universal
conjunction. Direct determinant arithmetic gives det(A)=4=2^(2^1), consistent
with Conjecture 4.3 in this instance.

## Evidence

`D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.lean` encodes
the full claim and proves its literal negation. Its constructions use the
actual cyclotomic field, actual integer ring, integral power basis and
generator-preserving equivalence described above. The private helpers
establish the all-input product law, the actual matrix and column, the
printed integer-vector witness and integral noninnerness on the live
derivation of `result`. The corresponding Blueprint gives the full
quantified statement and the same derivation. The Library note records the
versioned source, locators, attribution and license.

The original named target and its qualification are identified by
https://github.com/the-omega-institute/trureturing/issues/30116#issuecomment-6863321974.
The quadratic derivation and innerness classification is prior literature;
it is not claimed as a new classification here. The literature boundary is
the inspected source versions and the bounded qualification attached to
that target, not an exhaustive claim about all publications.

## Triage

- **Lean proved:** `result` refutes the full printed Conjecture 4.4 on its
  actual source domain through the iff. The proof is conservatively
  classified `proof_shape: bind-only`; its named external-problem basis is
  `admission_basis: open-problem-resolution`. No independent classification
  theorem or escape witness is claimed.
- **Lean proved in the counterinstance:** D is integer-linear, obeys the
  all-input twisted law, passes the literal printed test and is not
  integral-inner. The contradiction uses an actual integral coordinate.
- **Arithmetic consequence:** det(A)=4 while p^e=2. Dividing the adjugate
  column by 4 instead gives (0,1/2); the missing factor explains this
  failure. This calculation is not a general repaired-criterion theorem.
- **Logical boundary:** both extra sufficient implications have false
  antecedents here because c_0=1. Neither is independently refuted. The
  failure of the iff supplies no proof or refutation of those implications
  in general, and no conclusion premised on the full conjecture may retain
  that universal premise on the strength of this text.
- **Unresolved here:** Conjecture 4.3 for general prime powers, either
  sufficient assertion separately, a repaired denominator criterion and
  any corrigendum. No new quadratic classification is supplied.

## ASSUMED-UNVERIFIED

The source locators and qualification are bibliographic inputs from the
inspected versions and the identified target. No exhaustive subsequent
literature search or global priority certificate is asserted. Absence of a
journal reference or DOI from arXiv metadata does not establish absence of
a journal publication. No claim is made about the authors' intended repair
or any uninspected revision.

The article uses the arXiv nonexclusive distribution license,
http://arxiv.org/licenses/nonexclusive-distrib/1.0/, rather than a Creative
Commons license. Copyright remains with the authors. This dossier retains
mathematical paraphrase, references and the counterexample; it does not
redistribute the article or its source archive.
