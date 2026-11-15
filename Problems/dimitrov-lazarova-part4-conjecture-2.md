---
slug: dimitrov-lazarova-part4-conjecture-2
bibkey: dimitrovlazarova2026part4c2
doi: 10.3390/math14213935
url: https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/DimitrovPartIVC2.result
---

# Dimitrov and Lazarova Part 4, Conjecture 2

## Problem

For every natural $n\geq2$ and $k\geq1$,

$$
\frac{\varphi(n)^{3k}\psi(n)^{3k}+\psi(n)^{3k}\sigma(n)^{3k}
+\varphi(n)^{3k}\sigma(n)^{3k}}
{\varphi(n)^{2k}\psi(n)^{2k}\sigma(n)^{2k}}
\geq\frac{2(n^2-1)^{3k}+(n+1)^{6k}}{(n-1)^{2k}(n+1)^{4k}}.
$$

The functions are the actual Euler totient, Dedekind psi and positive-divisor
sum. Quotients and subtractions are real. The exact source is Section 4,
Conjecture 2, page 13 of the publisher PDF; definitions are on pages 1–2.
The immutable original preregistration is
[#30596 comment 6885699234](https://github.com/the-omega-institute/trureturing/issues/30596#issuecomment-6885699234).

## Motivation

This is the complete external power family. The source's Theorem 2 proves only
$k=1$. A numerator estimate without a corresponding denominator argument does
not establish this quotient inequality.

## Gap

The source calls this statement a conjecture. The bounded current-status screen
in [the source qualification](https://github.com/the-omega-institute/trureturing/issues/30596#issuecomment-6886094407)
identified no full settlement in its inspected scope. It is not a proof of
worldwide absence or historical priority.

## Route

Use the existing bounds $0<\varphi(n)\leq n-1$, $n+1\leq\psi(n)\leq\sigma(n)$.
With $x=(\psi/\varphi)^k$, $y=(\sigma/\varphi)^k$ and
$r=((n+1)/(n-1))^k$, these give $1\leq r\leq x\leq y$.
Two nonnegative factorizations show
$xy+x/y^2+y/x^2\geq x^2+2/x\geq r^2+2/r$.
Exact field normalization recovers the complete source formula.

## Falsifier

A natural pair $n\geq2$, $k\geq1$ violating the exact displayed inequality
would refute it. A failed proof attempt, a relaxed analytic counterexample or
a finite successful search does not settle the original universal event.

## Evidence

The exact declaration is
`D5/S3/Arith/Divisors/DimitrovPartIVC2.result`, proving the complete
`DimitrovPartIVC2.claim` above.
Its helper `ordered_ratio_bound` is private and consumed by `result`.
The classification is `proof_shape: bind-only` for the definition,
helper and endpoint: the proof consists of existing order laws, positivity,
explicit polynomial factorizations and field normalization. No escape witness
is claimed. The endpoint's admission basis is `open-problem-resolution`,
with the original preregistration linked above. The helper is retained only
as a consumed auxiliary on the result's live proof path.

The mirrored `Reg/D5/S3/Arith/Divisors/DimitrovPartIVC2.lean` supplies the
complete source-equivalence bridge, a rejected totient family witnessing
whole-family variation and sensitivity, and actual observational dependence.
Its continuation is explicitly unknown; it asserts no theorem about
inexhaustibility or undecidability.

The Scribe attaches
`OpenProblemResolutionClaim(ProblemSlugRef.Create("dimitrov-lazarova-part4-conjecture-2"), ResolutionKind.Proved)`
to the exact frozen result. This identifies the complete source assertion,
including every allowed natural exponent and every prime or composite input.

## Triage

### What the settlement shows

Proved by `D5/S3/Arith/Divisors/DimitrovPartIVC2.result`: the factorization
route treats arbitrary allowed exponents and composite as
well as prime inputs. At the analytic boundary $x=y=r$, both differences vanish.
This gives a sharp analytic envelope; a separate equality classification for
all arithmetic inputs remains open. The decisive mechanism is the pair of
nonnegative differences in the Route section, followed by exact normalization
to the original quotient. The source's Theorem 2 is the $k=1$ case; the result
establishes the full Conjecture 2. Consequences for other source questions
remain open. No priority claim is made.

## ASSUMED-UNVERIFIED

Worldwide literature coverage and priority remain unverified. Model families
are unverified, and repository priors were exposed. The original event,
preregistration, execution and reporting deadline are unchanged.
