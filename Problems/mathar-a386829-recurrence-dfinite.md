---
slug: mathar-a386829-recurrence-dfinite
bibkey: mathar2026a386829
doi: null
url: https://oeis.org/A386829
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/MatharA386829.result
---

# Mathar's recurrence and D-finiteness for OEIS A386829

## Problem

OEIS A386829, official export revision 12, defines Manyama's sequence by the
literal inclusive sum

$$
a(n)=\sum_{k=0}^{n}3^k2^{n-k}
\binom{2n+1}{k}\binom{2n-k}{n-k}.
$$

Mathar's FORMULA entry states:

> Conjecture D-finite with recurrence 2*n*a(n) +(-31*n+20)*a(n-1) +90*(-2*n+1)*a(n-2)=0.

The complete assertion consists of both the recurrence

$$
\forall n\in\mathbb N,\quad n\ge2\Longrightarrow
2n a(n)+(20-31n)a(n-1)+90(1-2n)a(n-2)=0
$$

and D-finiteness of the entire literal formal series

$$
A(z)=\sum_{n\ge0}a(n)z^n\in\mathbb Q[[z]].
$$

Precisely, there exist a natural number $r$ and a function
$p:\mathbb N\to\mathbb Q[z]$ such that some $p_j$ with $0\le j\le r$
is nonzero and

$$
\sum_{j=0}^{r}p_j(z)A^{(j)}(z)=0.
$$

Here $A^{(0)}=A$, higher derivatives are formal derivatives, and polynomials
are embedded in the rational formal power series ring. Sequence indices,
exponents and binomial coefficients are natural numbers; summands and the
recurrence are evaluated in the integers, and each series coefficient is cast
into the rationals. Both endpoints of every displayed finite sum are included.
The sequence offset is zero. The source gives no explicit recurrence onset;
$n\ge2$ is its entire domain with all three sequence indices nonnegative.
No assertion about unspecified negative indices is included.

## Motivation

The recurrence controls the whole sequence defined by the original sum.
The homogeneous differential equation certifies D-finiteness of every
coefficient of the same series, without a finite truncation, a replacement
sequence, or an assumption that another source formula is equivalent.

## Gap

The source labels the joint recurrence and D-finiteness claim a conjecture.
The finite source qualification recorded in
[issue #27081](https://github.com/the-omega-institute/trureturing/issues/27081)
and the library note did not identify a supplier of the full literal claim.
The compared entries A385669, A386763 and A386830 do not supply that complete
proof within the recorded scope. This is a bounded source and library finding,
not an exhaustive absence or worldwide priority claim.

## Route

The proof uses two auxiliary integer sequences

$$
b(n)=\sum_{j=0}^{n}5^j3^{n-j}\binom{n+j}{j},\qquad
c(n)=5^n\binom{2n}{n}.
$$

First expand $5^j=(2+3)^j$. Interchanging the finite triangular sums, applying

$$
\binom{n+j}{j}\binom{j}{i}
=\binom{n+i}{i}\binom{n+j}{n+i},\qquad
\sum_{j=i}^{n}\binom{n+j}{n+i}
=\binom{2n+1}{n-i},
$$

and reflecting the inclusive index range proves $a(n)=b(n)$ for every natural
$n$. Thus the argument derives the alternative expression from the original
sum rather than taking it as a premise.

The weighted binomial telescoping identity and the central-binomial identity
give

$$
4b(n+1)+18b(n)=7c(n+1),\qquad
(n+1)c(n+1)=10(2n+1)c(n).
$$

Eliminating $c$ from consecutive instances yields the recurrence, first in
forward-index form and then on the complete domain $n\ge2$. The literal
initial values are $a(0)=1$, $a(1)=13$ and $a(2)=204$. In particular the
$n=2$ recurrence reads $816-546-270=0$.

Coefficient comparison in $\mathbb Q[[z]]$ uses these initial coefficients
and the recurrence to prove

$$
(2-31z-180z^2)A'(z)-(11+270z)A(z)=15.
$$

Formal differentiation gives the homogeneous equation

$$
(2-31z-180z^2)A''(z)-(42+630z)A'(z)-270A(z)=0.
$$

The certificate has $r=2$, $p_0=-270$, $p_1=-(42+630z)$ and
$p_2=2-31z-180z^2$. The constant coefficient of $p_2$ is $2$, so this is a
nonzero homogeneous polynomial differential equation. No convergence,
analytic continuation or choice of an analytic branch is needed.

## Falsifier

A natural index $n\ge2$ at which the original inclusive integer sum violates
the recurrence would contradict the first conjunct of
`D5/S3/ArithSums/MatharA386829.result`. A nonzero coefficient of the displayed
homogeneous formal differential expression would contradict its second
conjunct and the explicit certificate in its proof.

## Evidence

The mathematical source is `D5/S3/ArithSums/MatharA386829.lean`; the public
objects are `a`, `series` and `result`. The theorem proves the conjunction of
the full recurrence and the nonzero homogeneous differential equation for
the series built directly from `a`. Its axiom closure is limited to
`Classical.choice`, `Quot.sound` and `propext`.

The private steps `choose_product`, `hockey` and `literal_eq_auxiliary`
establish the original-sum bridge; `auxiliary_step`, `central_step` and
`recurrence` establish the integer relation; `formal_equation` and
`homogeneous_equation` produce the formal series certificate. The ingredients
reuse pinned Mathlib binomial-product and hockey-stick identities,
central-binomial recurrence, finite-sum rearrangements, algebra and formal
power series differentiation. No independent frozen D5 supplier is an input.
The canonical Blueprint binds its `Proved` resolution claim to `result`.

## Triage

Tier 1 external named OEIS conjecture, with a full universal symbolic
resolution rather than a bounded positive instance. The admission basis is
`open-problem-resolution`, linked to
[the exact preregistered event](https://github.com/the-omega-institute/trureturing/issues/27081#issuecomment-6672416300).
Utility is `none`. All nine authored theorem proofs are `bind-only` under the
repository's inlining and normalization rule; the auxiliary statements have
actual mathematical consumers. This application of existing ingredients
claims no new proof technique or escape witness.

### What the settlement shows

- **Proved by `D5/S3/ArithSums/MatharA386829.result`:** the exact published
  recurrence and D-finiteness hold together for the original inclusive sum.
  The decisive mechanism is the finite triangular binomial transformation,
  followed by elimination of the central-binomial auxiliary sequence.
- **Proved inside that result:** the alternative sum equals the original sum
  at every natural index, and a second-order nonzero homogeneous equation
  annihilates the entire rational formal series. These are steps of this
  proof, not additional exported settlement claims.
- **Open in this delivery:** minimal homogeneous differential order,
  analytic asymptotics and parameterized versions of the binomial transform.
  The order-two certificate does not assert minimality. No negative-index
  convention, generalized parameter theorem or analytic consequence is
  established here.
- **Source dependency boundary:** the result supplies the complete conjectured
  recurrence and D-finiteness. It does not certify every other formula or
  related sequence in the entry, and no dependency of other named open
  questions on this conjecture is established in the recorded source scope.

## ASSUMED-UNVERIFIED

Worldwide openness, priority and exhaustive absence of earlier proofs remain
unverified beyond the finite source qualification and library search.

The four-slot escape audit is unfinished, as disclosed in
[the concrete audit issue](https://github.com/the-omega-institute/trureturing/issues/27081#issuecomment-6672643205).
The attempted infinite integer coefficient-family realization must reconstruct
all three recurrence occurrences and the whole `PowerSeries.mk` family from
one source law. Producer-checked selectors and rigid universes, whole-family
intervention, variation/sensitivity and observational-dependence proofs remain
missing. There is no retained Reg source, compiled registration client or
validated audit certificate. Mathematical kernel verification does not supply
those missing registration obligations.
