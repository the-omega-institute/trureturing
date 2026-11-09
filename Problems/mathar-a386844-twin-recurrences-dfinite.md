---
slug: mathar-a386844-twin-recurrences-dfinite
bibkey: mathar2026a386844
doi: null
url: https://oeis.org/A386844
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/MatharA386844.result
---

# Mathar's A386844 twin recurrences and ordinary D-finiteness

## Problem

Manyama's sequence in OEIS A386844, revision 16, is the literal inclusive sum

$$
a(n)=\sum_{k=0}^{n}\binom{3n+2}{k}\binom{3n-k}{n-k},\qquad n\in\mathbb N.
$$

Both endpoints and n=0 are included. Mathar's two FORMULA entries conjecture
D-finiteness with the respective signed recurrences

$$
\begin{aligned}
R_3(n)={}&3n(2n-1)a(n)+(-353n^2+1009n-672)a(n-1)\\
&+(3938n^2-15029n+13872)a(n-2)-399(3n-4)(3n-5)a(n-3)=0,\\
R_2(n)={}&n(2n-1)(5n-8)a(n)+(-145n^3+362n^2-264n+63)a(n-1)\\
&+3(3n-1)(5n-3)(3n-2)a(n-2)=0.
\end{aligned}
$$

The assertion requires R3(n)=0 for every natural n >= 3, including 3, and
R2(n)=0 for every natural n >= 2, including 2. These are the disclosed
natural-lag interpretations in
[the preregistered event](https://github.com/the-omega-institute/trureturing/issues/27973#issuecomment-6717894912);
OEIS supplies offset 0,2 but does not state either onset. Polynomial and
signed recurrence arithmetic is in the integers after casting n and a(n);
only lag indices use natural subtraction.

For the same complete ordinary series

$$
A(z)=\sum_{n\ge0}(a(n):\mathbb Q)z^n\in\mathbb Q[[z]],
$$

the third conjunct requires a natural r and polynomials
$p:\operatorname{Fin}(r+1)\to\mathbb Q[z]$ with some nonzero p(j), such that

$$
\sum_{j=0}^{r}p_j(z)D^j A(z)=0.
$$

D denotes formal differentiation, with D^0 the identity. This is a finite
nonzero homogeneous operator on the whole ordinary series, with no convergence
hypothesis or substitution of an exponential series or initial-value proxy.

## Motivation

The joint assertion determines the two conjectured relations for the original
sum on their complete specified domains. The formal differential certificate
applies to every coefficient of that same sequence.

## Gap

The immutable revision 16 export labels both relations conjectures. The
bounded source qualification in issue #27973 and
`Library/AnalyticClosure/mathar2026a386844.md` identifies no complete
prior settlement within its stated readings. General Lagrange inversion and
coefficient extraction are suppliers, without a target-specific native bridge
or the full conjunction in their statements. No exhaustive absence or priority
claim follows from this search scope.

## Route

The original sum is identified, for every natural n, with the coefficient

$$
[x^n]H(x)\phi(x)^n,\qquad
H(x)=\frac{(1+x)^2}{1-x},\qquad
\phi(x)=\frac{(1+x)^3}{(1-x)^2}.
$$

Formal Lagrange substitution and the compositional inverse construct w with
zero constant term and

$$
z(1+w)^3=w(1-w)^2,\qquad A=\frac{(1+w)^3}{1-5w}.
$$

The denominators are units in the formal series ring. With theta=z D,
transported polynomial numerator identities give

$$
O_3 A=8z+532z^2,\qquad O_2 A=-8z.
$$

Here O3 and O2 are the explicit Euler operators in the Lean source associated
with the respective recurrence coefficients. Coefficient extraction gives the
two signed relations at every required index. Applying theta-1 to the second
forcing relation and cancelling z^2 yields the homogeneous operator of order
four, whose coefficients in ascending derivative order are

$$
\begin{aligned}
p_0&=420,\\
p_1&=3612z-177,\\
p_2&=4593z^2-1209z+6,\\
p_3&=1539z^3-943z^2+29z,\\
p_4&=135z^4-145z^3+10z^2.
\end{aligned}
$$

The nonzero constant polynomial p0 certifies nonzeroness. All operations and
identifications are formal; no analytic branch is assumed.

## Falsifier

An index n >= 3 violating R3, an index n >= 2 violating R2, or a nonzero
coefficient of the displayed homogeneous expression for the literal A would
contradict the corresponding conjunct of
`D5/S3/ArithSums/MatharA386844.result`.

## Evidence

The Lean source is `D5/S3/ArithSums/MatharA386844.lean`, with the single public
settling theorem `result : P`. Definitions a, R3, R2, A, D and op spell out
all three clauses. Its axiom closure is `propext`, `Classical.choice` and
`Quot.sound`.

The direct frozen suppliers are
`D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.lagrange_subst`
and `D5/S1/Recurrence/A308815DFiniteRecurrence.euler_coeff`. Pinned Mathlib
supplies binomial convolution and inverse coefficients, compositional
inversion, formal derivatives, unit cancellation and normalization.

The source-owner Reg mirror retains a compiled typed
`DependentFamily.Registration arena P`: the literal summand is its readout,
and one actual realization reconstructs both recurrences and the complete
series. Its axiom closure is the same standard set. This family evidence does
not complete the outer `Contract.Registration` or source-occurrence binding.

## Triage

Tier 1 externally named Mathar conjectures on Manyama's sequence, resolved as
one exact conjunction. The proposed admission basis is
`open-problem-resolution`, subject to the repository's delivery checks;
utility is `none`. This is a universal symbolic proof, not a positive finite
instance or bounded enumeration. No escape witness or new proof technique is
claimed. Every theorem has proof shape `bind-only` under the repository's
inlining and normalization rule:

| Declaration | Actual live consumer |
| --- | --- |
| native_coefficient | native_parametrization |
| weighted_lagrange | native_parametrization |
| native_parametrization | theta_powers |
| theta_numerator_step | theta_powers |
| theta_powers | forcing |
| order3_numerator | forcing, first conjunct |
| order2_numerator | forcing, second conjunct |
| forcing | recurrences; homogeneous |
| recurrences | result, first and second conjuncts |
| homogeneous | result, third conjunct |
| result | exact external conjunction; Reg.source_registration |

The auxiliary definitions are consumed proof data. The result uses the
external open-problem exception; helpers use the consumed-helper rule.

### What the settlement shows

- **Proved by `D5/S3/ArithSums/MatharA386844.result`:** both original signed
  recurrences hold on their full specified domains, and the same entire
  ordinary rational series has a nonzero homogeneous polynomial annihilator.
  The decisive mechanism is the native all-index coefficient bridge followed
  by formal Lagrange inversion and operator transport.
- **Proved inside that result:** the forcing terms have support below the
  respective recurrence onsets, and the displayed order-four certificate
  annihilates the full series. These are proof ingredients, not additional
  exported settlement claims.
- **Open in this delivery:** minimal annihilator order, parameterized variants,
  analytic asymptotics and the validity of other formulas in the OEIS entry.
  The order-four witness asserts no minimality or convergence.
- **Source dependency boundary:** no dependency of another named open problem
  on these conjectures is established in the recorded source scope. No claim
  for the neighbouring sequences follows merely from this specialization.

## ASSUMED-UNVERIFIED

Worldwide openness, priority and exhaustive semantic absence of earlier proofs
remain unverified beyond the bounded qualification in issue #27973.

The outer escape audit is unfinished under the
[linked-issue exception](https://github.com/the-omega-institute/trureturing/issues/27973#issuecomment-6718421807).
The nullary theorem proposition exposes R3, R2 and op on A, but the literal
summand lies behind additional R3/R2/A/a definitions. A faithful raw
source-selection and occurrence binding across all three conjuncts has not
been supplied. The retained typed family proof is successful evidence, not
`declared_validated`; no judge change or target weakening supplies the missing
outer binding.
