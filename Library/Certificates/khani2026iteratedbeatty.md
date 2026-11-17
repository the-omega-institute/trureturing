---
bibkey: khani2026iteratedbeatty
authors: Mohsen Khani, Ali N. Valizadeh and Afshin Zarei
year: 2026
title: A Note on Iterated Beatty Sequences
doi: null
url: https://arxiv.org/abs/2607.12817v1
claim: Question 1 asks whether the main iterated Beatty range characterization extends to irrational moduli between one and its original upper threshold.
strata_touched:
  - D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation
license: citation-only
triage: anchor
---

# Iterated Beatty range characterization

Source: https://arxiv.org/abs/2607.12817v1

The main theorem on printed page 1 assumes an irrational real modulus
$\alpha>(3+\sqrt5)/2$ and a positive integer $n$. It characterizes membership
of a natural number $x$ in the range of the actual composition $f_\alpha^n$,
where $f_\alpha(k)=\lfloor\alpha k\rfloor$, by

$$
1-\frac1\alpha<\left\{\frac x\alpha\right\}<1
$$

and, for every $2\le i\le n$,

$$
1-\frac2\alpha<\left\{\frac x{\alpha^i}\right\}
-\frac{\{x/\alpha^{i-1}\}}\alpha<1-\frac1\alpha.
$$

Here $\{t\}=t-\lfloor t\rfloor$. Powers in the fractional tests are real
powers with natural exponents; the iterated range uses repeated floor maps,
not the single map $k\mapsto\lfloor\alpha^n k\rfloor$.

Question 1, printed page 8, asks:

> A natural question is whether our theorem holds also for irrationals
> belonging to the following set:
> (1, 2.618∼) = (1, 2.118∼) ∪ (2.118∼, 2.618∼).

The displayed typography is normalized. The exact upper endpoint inherited
from the theorem is $c=(3+\sqrt5)/2$. The internal split $\rho$ is the greatest
real root of $t^4-2t^3-t+1$. The registered extension is the entire interval
$(1,c)$, including $\rho$, despite its omission from the printed open union.

The bounded source reading does not settle whether the source's naturals
include zero. The registered claim uses positive natural inputs and positive
natural preimages. Its counterexample has $\alpha=\sqrt2$, $n=3$, $x=2$ and
preimage $2$. It consequently refutes either natural-number convention;
it does not rely on the behavior at zero. Since the polynomial is negative
at $2$ and positive at $3$, continuity gives a root greater than $2$, hence
$\sqrt2<3/2<2<\rho$. The same witness lies in the lower printed branch.
The original theorem for $\alpha>c$ is not refuted.

The formal module defines the source's map directly on natural numbers using
Mathlib's natural floor of the real product $\alpha k$, and uses
`Function.iterate` for composition. For $\alpha>1$ each positive integer $k$
satisfies $k\le\lfloor\alpha k\rfloor$, so all iterates stay positive.
The real products are nonnegative; natural floor consequently has the same
integer value as the source's floor at every intermediate step.

The exact calculation is $2<2\sqrt2<3$, so $f_{\sqrt2}(2)=2$ and
$f_{\sqrt2}^3(2)=2$. Meanwhile $\{2/(\sqrt2)^2\}=0$ and
$\{2/(\sqrt2)^3\}=1/\sqrt2$. The index-three middle expression is therefore
$1/\sqrt2>1-1/\sqrt2$, contradicting its required strict upper bound.

The source and preregistration are associated with repository issue #29668.
Admission is `open-problem-resolution`, Tier 1, small-case; the expected
proof shape is `bind-only`, through pinned Mathlib floor and square-root
results. This identifies an application to the named question, not a new
general floor or square-root theorem.

The bounded literature screen found no exact resolution in the inspected
D5/private declarations, Library/Problems/public registry scopes or the
formal-conjectures revision a425ca3eb797fe927cb88c950565fdcbbbbada70.
The current arXiv reading identifies v1 and still poses Question 1.
Semantic Scholar's inspected record has an empty citation list. The read
Chew–Tanny author manuscript concerns restricted quadratic-modulus and
commutator results, and the inspected Dekking results concern restricted
quadratic double iterates; neither supplied this exact criterion.
The Chew–Tanny publisher final text returned 403, and its identity with
the author manuscript is unverified. OpenAlex returned 429, and MathDB
challenge pages remained unread. These are bounded source readings;
no exhaustive novelty or worldwide priority claim is made.

## Verified locator

https://arxiv.org/abs/2607.12817v1, main characterization on printed page 1
and Question 1 on printed page 8. The inspected PDF SHA-256 is
`5907ce19916db99b8e34fbecee5ce6bf9d693f2a769d2267bfb9952c2d5f037f`.
