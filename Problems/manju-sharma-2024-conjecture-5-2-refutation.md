---
slug: manju-sharma-2024-conjecture-5-2-refutation
bibkey: manjusharma2024twisted
doi: null
url: https://arxiv.org/abs/2412.03507v2
triage: theorem
motivation_gids:
  - D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.result
---

# Manju–Sharma's full printed Conjecture 5.2

## Problem

Praveen Manju and Rajendra Kumar Sharma, *Twisted Derivations in Algebraic
Number Fields*, [arXiv:2412.03507v2](https://arxiv.org/abs/2412.03507v2),
Section 5.2, Conjecture 5.2, asks for the following conjunction. The primary
TeX member is `Twisted_derivations_in_algebraic_number_fields.tex` at
https://arxiv.org/src/2412.03507v2, lines 2240–2242, with SHA-256
`61eac8e439f53269a30a61579d0c822058c9752410a3f65fb5c4e67309b9ce18`.
The versioned source, inherited hypotheses and license are identified in
the [Library note](../Library/Quad/manjusharma2024twisted.md).

Let p be any rational prime, k a natural number unequal to one, and
n=p^k at least three. Let K=Q(zeta), with zeta a primitive n-th root,
and O its full ring of algebraic integers Z[zeta]. Put
N=p^(k-1)(p-1) and use the ordered integral power basis
(1,zeta,...,zeta^(N-1)). Let sigma and tau be distinct nonzero unital
integer-algebra endomorphisms of O, with
sigma(zeta)=zeta^u and tau(zeta)=zeta^v. The distinct representatives u,v
are positive, less than n and coprime to n. In increasing exponent order,
write their difference as p^e m, where e is nonnegative, m is positive
and p does not divide m. This is the domain inherited from Conjecture 4.3;
its conjectural determinant conclusion is not assumed.

Let Der be the integer module of all integer-linear D:O to O satisfying

$$D(xy)=D(x)\tau(y)+\sigma(x)D(y)\qquad(x,y\in O).$$

Let Inn be its submodule consisting of maps for which one gamma in O
satisfies D(x)=gamma tau(x)-sigma(x)gamma for every x. Definition 2.1
defines outer derivations as the quotient Der/Inn. The Remark at TeX
lines 156–158 identifies non-inner representatives with nonzero quotient
classes, which is the meaning of an outer D in the criterion below.

The integer matrix A is the actual matrix of multiplication by
tau(zeta)-sigma(zeta) in the ordered power basis. The integer column C
is the actual coordinate column of D(zeta). Conjecture 5.2 asserts,
universally over these objects and every D in Der, the conjunction

$$\begin{aligned}
 [D]\ne0\text{ in }\mathrm{Der}/\mathrm{Inn}
 &\quad\Longleftrightarrow\quad
 p^{-e}\operatorname{Adj}(A)C\notin\mathbb Z^N,\\
 \mathrm{Inn}&\subsetneq\mathrm{Der},
 \qquad\text{equivalently, }\exists D\in\mathrm{Der},\ [D]\ne0.
\end{aligned}$$

Adj means the classical adjugate and the denominator is literally p^e.
For a reversed exponent pair, exchange the twists when writing the
positive factorization. Commutativity preserves the twisted law, negating
the integral inner multiplier preserves Inn, and A changes to -A.
The identity Adj(-A)=(-1)^(N-1)Adj(A) preserves integrality of the test
vector. Thus both orders of every admissible distinct pair are included.

| Source clause | Lean counterpart |
| --- | --- |
| Every prime p and k unequal to one with p^k at least three | The initial binders and hypotheses of `claim`; the size condition excludes k=0. |
| Actual rational cyclotomic field and primitive root | `K`, its `Field`, `NumberField`, `IsCyclotomicExtension` and `NeZero` instances, and `hζ : IsPrimitiveRoot ζ (p^k)`. |
| Full integer ring and ordered integral powers | `RingOfIntegers K`, `z := hζ.toInteger`, and every `PowerBasis` with generator z and dimension N; `basis_eq_pow` fixes its order. |
| Distinct nonzero twists and admissible representatives | Integer-algebra endomorphisms, `σ ≠ τ`, positive bounded coprime u,v, distinctness and both root-image equations. Unital maps of this nontrivial ring are nonzero. |
| Positive source factorization in either order | Natural e,m, `0 < m`, `¬ p ∣ m`, and `v = u + p^e*m ∨ u = v + p^e*m`. |
| Integer linearity and the law on all inputs | Membership in `derivations σ τ`. |
| One integral inner multiplier on all inputs | `inner σ τ`, using the existing `IsInner` definition. |
| Actual outer class | `outerClass σ τ D`, the canonical map to the quotient by `inner`. |
| Defined A, C and literal integrality test | `Algebra.leftMulMatrix`, `pb.basis.repr (D.val z)` and the unchanged `PrintedIntegralTest`. |
| Criterion together with universal strict inclusion | The three conjuncts of `claim`: the all-D biconditional, `inner σ τ < ⊤`, and existence of a nonzero outer class, for every admissible pair. |
| Negation of the entire original conjunction | The literal `result : ¬ claim`. |

## Motivation

The question seeks an integral test for a nonzero outer class from the
generator value D(zeta), and also asserts existence of such a class for
every admissible pair. A faithful refutation must retain both assertions
in its target. A freely chosen matrix, a generator-only product check or
innerness over the fraction field would not answer this question.

## Gap

The printed p^e denominator can make the adjugate vector integral while
the rational solution of AX=C remains nonintegral. The actual fourth-root
case has det(A)=4 and p^e=2. The separate strict-inclusion assertion is
not contradicted by this obstruction: in this same case a nonzero outer
class exists.

## Route

Reuse the actual fourth cyclotomic field K4 and O4=`RingOfIntegers K4`
from `ManjuSharmaConjectureFourFour`. Its generator-preserving integer
algebra equivalence with Gaussian integers is proved using the actual
integral power basis. Set sigma to the identity, tau to transported
conjugation, and D(a+bz)=b, where z^2=-1. The existing all-input product
law makes D an element of the actual module Der; it is not merely an
assignment to z.

The quotient theorem `Submodule.Quotient.mk_eq_zero` gives [D] nonzero
exactly when D is not inner. The private `outer_nonzero_iff` applies this
theorem and is used in the proof of `result`. Take
p=k=2, n=4, u=1, v=3, e=m=1. The existing primitive-root, ordered-basis,
root-image, twisted-law, non-innerness and printed-test results supply
the exact counterinstance. Primitive-root power injectivity proves that
the twists are distinct.

## Falsifier

Multiplication by tau(z)-sigma(z)=-2z in the ordered basis (1,z) gives

$$A=\begin{pmatrix}0&2\\-2&0\end{pmatrix},\qquad
C=\begin{pmatrix}1\\0\end{pmatrix},\qquad
\operatorname{Adj}(A)=\begin{pmatrix}0&-2\\2&0\end{pmatrix},\qquad
\tfrac12\operatorname{Adj}(A)C=\begin{pmatrix}0\\1\end{pmatrix}.$$

The printed vector is integral. An integral inner multiplier gamma=a+bz
would give 1=gamma(-z)-z gamma=2b-2az on evaluation at z, forcing 1=2b
in the integers. Thus D is not inner and [D] is nonzero. The forward
direction of the printed biconditional would make the same vector
nonintegral. This contradiction refutes the whole universal conjunction.
Table 3 has the opposite matrix sign; the source's defining multiplication
operator determines the sign above, and changing the overall sign does
not change integrality.

## Evidence

The [Lean module](../D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.lean)
defines the actual derivation submodule, inner submodule and quotient map,
then proves the literal negation of the full claim. Its
[Blueprint](../Blueprint/D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.md)
exposes the same quantified statement and contradiction and binds the
result to this single original problem. The
[existing Conjecture 4.4 module](../D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.lean)
supplies the actual cyclotomic counterexample, rather than a new
classification of quadratic derivations. The axiom closure is contained
in {propext, Classical.choice, Quot.sound}.

The original full target is [#30268](https://github.com/the-omega-institute/trureturing/issues/30268).
Its [result](https://github.com/the-omega-institute/trureturing/issues/30268#issuecomment-6873440826)
and immutable [REFUTED terminal](https://github.com/the-omega-institute/trureturing/issues/30268#issuecomment-6873441119)
refer to that same conjunction. No separate resolution of the
strict-inclusion assertion is inferred from them.

## Triage

- **Lean proved:** `result` refutes the full printed Conjecture 5.2 through
  its criterion. Its conservative classification is `proof_shape: bind-only`
  and `admission_basis: open-problem-resolution`; no escape witness or new
  quadratic classification is claimed.
- **Consumed helper:** the private bind-only `outer_nonzero_iff` is used
  by `result` to connect the actual quotient class to integral
  non-innerness. It is not an independent mathematical contribution.
- **Counterinstance:** the actual integer-linear D obeys the full twisted
  law, has nonzero outer class and passes the literal printed test.
- **Logical boundary:** universal strict inclusion remains open here and
  is not separately refuted. The exhibited class supports strict inclusion
  for this particular pair. No corrected denominator criterion is refuted.
- **Neighboring candidate:** an adjugate criterion divided by det(A),
  with its necessary hypotheses and integer-ring bridges, is a possible
  correction. Standard adjugate linear algebra does not by itself supply
  those bridges. No general corrected cyclotomic criterion is proved here;
  this candidate creates no additional resolution claim.

## ASSUMED-UNVERIFIED

The literature qualification is bounded by the source versions and
queries identified in the original target and the Library note. It is
not an exhaustive subsequent literature search or a global priority
certificate. The source's quadratic classification is prior literature.
No assertion is made about an uninspected revision, corrigendum or the
authors' intended repair.

The article uses the arXiv nonexclusive distribution license,
http://arxiv.org/licenses/nonexclusive-distrib/1.0/; copyright remains
with the authors. This dossier retains mathematical paraphrase,
references and the counterexample, not the article or its source archive.
