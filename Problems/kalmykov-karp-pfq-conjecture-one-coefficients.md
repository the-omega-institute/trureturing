---
slug: kalmykov-karp-pfq-conjecture-one-coefficients
bibkey: kalmykovkarp2017pfq
doi: null
url: https://arxiv.org/abs/1611.06724v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/HypergeometricShiftTuran/Defs.claim
  - D5/S3/Analytic/HypergeometricShiftTuran/Result.result
---

# Coefficients of the shifted Gamma product Turanian

## Problem

The source is arXiv:1611.06724v1, section 3, page 6. The supplied source
text states:

> Theorem 3. If p ≤ q and conditions (13) are satisfied, then ∆f(α, β; x) ≥ 0 for x ≥ 0, µ, β ≥ 0 and α ∈ N, where ∆f(α, β; x) is defined in (9) with f from (10). Moreover, if α ≤ β + 1, then δm ≥ 0 for all m ∈ N0.
> Conjecture 1. All conclusions of Theorem 3 hold for all α, β ≥ 0 if µ ≥ 1.

For positive parameter vectors of lengths $p$ and $q$, put

$$
c(t)=\frac{\prod_{i=1}^p\Gamma(a_i+t)}{\prod_{j=1}^q\Gamma(b_j+t)},
\qquad
f(\mu;x)=\sum_{n=0}^{\infty}c(\mu+n)\frac{x^n}{n!}.
$$

The coefficient of degree $m$ in
$f(\mu+\alpha;x)f(\mu+\beta;x)-f(\mu;x)f(\mu+\alpha+\beta;x)$ is

$$
\delta_m=\sum_{k=0}^m
\frac{c(\mu+\alpha+k)c(\mu+\beta+m-k)
-c(\mu+k)c(\mu+\alpha+\beta+m-k)}{k!(m-k)!}.
$$

For $p\le q$, condition (13) consists of the inequalities

$$
\frac{e_{q-j}(\mathbf b)}{e_{p-j}(\mathbf a)}
\le\frac{e_{q-j-1}(\mathbf b)}{e_{p-j-1}(\mathbf a)}
\qquad(0\le j<p),
$$

where $e_0=1$. Empty parameter vectors are allowed. In particular,
the condition is vacuous at $p=0$.
`Defs.claim` retains all parameter vectors and all coefficient degrees,
with $\mu\ge1$, $\alpha,\beta\ge0$ and $\alpha\le\beta+1$.

## Motivation

The coefficient conclusion is one of the conclusions asserted by the
conjecture. A single negative coefficient under these hypotheses suffices
to refute that assertion, independently of the value of the Turanian at
nonnegative real arguments.

## Gap

The source targets `Result.result : ¬ Defs.claim` through the family
`Result.half_parameter_family_neg`. Lean validation and axiom closure
have not been checked. This dossier does not assert a kernel-verified
settlement or a literature priority conclusion.

## Route

Take $p=0$, $b_j=1/2$, $\mu=1$, $\alpha=\beta=1/2$ and $m=1$. Then
$c(t)=\Gamma(t+1/2)^{-q}$, and the two summands give

$$
\delta_1=2(1/2)^q-
\left(\frac{16}{9\pi}\right)^q-
\left(\frac{16}{15\pi}\right)^q.
$$

The general half-integer Gamma formula supplies the required values.
The bound $\pi<3.15$ gives $32/(9\pi)>640/567>1$, and exact rational
arithmetic gives $(640/567)^6>2$. Monotonicity of natural powers gives
$(32/(9\pi))^q>2$ for $q\ge6$. Thus the middle term exceeds the positive
leading term, and the last term is strictly positive before subtraction.
Specialization at $q=6$ contradicts coefficient nonnegativity.

## Falsifier

A source mismatch concerning empty parameter vectors, the symmetric
ratio condition, or the conjecture's shift restrictions would invalidate
this correspondence. The finite sum must retain both degree-one terms
and both factorial denominators. The identity for the coefficient and
the family inequality must compile without additional hypotheses,
proof placeholders, or new axioms.

## Evidence

The mathematical source is the quoted version and locator above.
The Lean sources are `D5/S3/Analytic/HypergeometricShiftTuran/Defs.lean`
and `D5/S3/Analytic/HypergeometricShiftTuran/Result.lean`.
The family theorem is used by the designated refutation at $q=6$.
There is no compiled Lean or registration verdict for these sources.

## Triage

The coefficient family concerns every natural $q\ge6$ and uses a positive
base parameter and positive shifts. It does not test the integer-shift
theorem at a noninteger shift. Negativity of one Taylor coefficient
does not determine the sign of the whole Turanian on the nonnegative
real axis. The threshold six is sufficient; no minimality assertion is
included. The reciprocal Gamma sequence problem has different
coefficients and is a separate assertion.

## ASSUMED-UNVERIFIED

The original PDF and preregistration issue have not been retrieved
independently; the quotation, empty-vector convention and source
identification are supplied premises. External literature and priority
checks are not represented as complete. The source bibliography key is
a local label and is not an independently verified bibliographic record.
