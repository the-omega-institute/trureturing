---
slug: oeis-a263160-first-zero-diagonal-limit
bibkey: kotesovec2026a263160
doi: null
url: https://oeis.org/A263160
triage: theorem
motivation_gids:
  - D5/S1/Words/LatticePaths/KotesovecA263160
---

# First-zero lattice paths and the A263160 diagonal limit

## Problem

The preregistered historical target is OEIS A263160 revision 21, which defines
`a(n)=A263159(n,n)` and quotes:

> Conjecture: Limit_{n->oo} a(n)^(1/n^2)/n = 1/log(2). - Vaclav Kotesovec, Nov 09 2026

A263159 revision 16 counts finite ordered paths from `(h,...,h)` in `d`
labelled coordinates. A step decrements a nonempty subset by one. The path
stops at the first zero in any coordinate. Simultaneous first zeros give one
terminal word. Zero dimension or zero height gives the immediate empty path,
count one. The logarithm is natural and the exponent is a real power.
The target is the limit along every natural index, with no fixed-dimension
hypothesis or subsequence restriction.

The current source is [A263160 revision 24](https://oeis.org/A263160), whose
revision timestamp is 2026-11-13 16:51:52 Singapore time. It instead asserts

`a(n) ~ c*n^(n*(n-3/2)+1)/(Pi^(n/2)*log(2)^(n*(n-1)))`,

with `c=10.75366283...`, signed Vaclav Kotesovec, November 13, 2026.
The [public history](https://oeis.org/history?seq=A263160) records the original
limit in #17, deletion of its conjecture line in #22, the stronger assertion
in #23 and approval in #24. Approval is an editorial state, not a proof.
The current JSON and history supply no proof, exact definition of `c` or
error bound. A proof of the stronger assertion would cover the historical
limit, but public proof coverage remains ASSUMED-UNVERIFIED. The historical
target and the exact Lean limit in Formal result remain the scope here;
the stronger asymptotic is not a replacement target or an additional result.

## Motivation

The number of coordinates grows together with the initial height. Thus a
fixed-dimension endpoint asymptotic does not answer this question. The stopping
rule also differs from ending with all coordinates zero: a coordinate may
reach zero while the others remain positive.

## Gap

The source question requires uniform control as both height and dimension
grow. An exact endpoint formula or a fixed-dimension asymptotic alone does
not supply that control. The counting bridge and estimates below close this
mathematical gap for the historical limit.

### Formal result

`D5.S1.Words.LatticePaths.KotesovecA263160.diagonal_limit` proves

```lean
Tendsto (fun n : ℕ => Real.rpow (a n : ℝ) (1 / (n : ℝ)^2) / (n : ℝ))
  atTop (nhds (1 / Real.log 2))
```

Here `a n = paths n n`; `paths` counts the literal finite first-zero words,
not a series chosen to have the desired limit. The finite range is exhaustive
by `first_zero_length_bound`: the length is at most `d*(h-1)+1`, which is at
most `d*h` when both parameters are positive; either zero parameter permits
only the empty word. The same bound truncates the terminal-word sum in the
counting identity. The proof only discards the cofinite indices
below two. It makes no fixed-dimension or subsequence assumption.

Preregistration is [issue #29912](https://github.com/the-omega-institute/trureturing/issues/29912).
The typed Proved resolution claim covers the historical limit. Final independent
review, exact-head required checks and delivery to dev remain separate obligations.
The source-bound audit is unfinished under
[issue #29924](https://github.com/the-omega-institute/trureturing/issues/29924).
No resolved-problem KPI is claimed.

## Route

### Counting bridge

For `m=h-1`, let `I_t` count words of nonempty labelled coordinate subsets
in which every coordinate occurs at most `m` times. Such a word has length
at most `d*m`. Put `I = Sum_{t=0..d*m} I_t`.

Appending any of the `2^d-1` nonempty steps to an internal word either stays
internal or reaches its first zero. These outcomes are disjoint and exhaustive.
A simultaneous first zero remains one word. Every nonempty internal word has
one parent; the empty internal word is unique. Summing the append partition
therefore proves, for `d>0`,

`paths(d,m+1) = 1 + (2^d-2)*I`.

For `P_m(k) = Sum_{r=0..m} binomial(k,r)`, transposing an incidence matrix
with optional empty columns into its independent labelled rows gives

`P_m(k)^d = Sum_{t=0..k} binomial(k,t)*I_t`.

The original generic optional-letter insertion theorem in
`D5/S1/Words/LatticePaths/MatharA379464Counting` supplies insertion of empty
columns. Its original `count` and `insertion_formula` declarations are exposed
in place with their proofs preserved. The shifted geometric binomial identity
from pinned Mathlib then yields the convergent positive sum

`Sum_{k>=0} 2^(-k)*P_m(k)^d = 2*I`.

The endpoint binomial-moment representation is prior work: Dan Dima's
[A126086](https://oeis.org/A126086) formula, Eger
[arXiv:1511.00622v2](https://arxiv.org/abs/1511.00622v2), section 5.5,
equation (3), page 10, and Bala's [A262809](https://oeis.org/A262809) formula.
Dima and Eger allow arbitrary finite positive dimension and prescribed
nonnegative endpoint coordinates. Summing those endpoints over the box
`0 <= r_i <= m` gives this truncated-binomial moment. The counting/moment
representation is not claimed as a new external mathematical solution.

### Uniform estimates

Vandermonde's identity and the standard binomial factorial bounds give

`(k+1-m)_+^m/m! <= P_m(k) <= (k+m)^m/m!`.

All parameters remain free. With `N=m*d`, every positive-series term is a
lower bound for `2*I`, while the sum-integral/Gamma upper estimate gives

`2*I <= 2^(m+1)*N! / ((log 2)^(N+1)*(m!)^d)`.

The upper comparison uses a monotone polynomial and an antitone exponential
as separate factors; their product is not assumed globally antitone. For the
lower bound choose `k = ceil(N/log 2)+m`. Taking logarithms and using the
public Mathlib factorial-log estimates gives

`N*log(N/log 2)-N-(m+1)*log 2-d*log(m!) <= log(2*I)`

and

`log(2*I) <= (m+1)*log 2+log(N!)-(N+1)*log(log 2)-d*log(m!)`.

The terminal-count relation transfers these estimates to the source count.
For every `n>=2`, the compiled quantitative estimate is

`abs(log(a(n))-n^2*(log(n)-log(log 2)))`

`<= n*(4*log(n)+6+2*abs(log(log 2)))`.

Division by `n^2`, the limit `log(n)/n -> 0`, and continuity of the exponential
prove the exact real-root limit. Positivity follows from the finite count;
the conversion to `Real.rpow` does not introduce an extra hypothesis.

## Falsifier

A mismatch with the literal first-zero word count invalidates the source
bridge. A counterexample to the uniform estimates invalidates that route.
A finite prefix agreement, fixed-dimension theorem or conditional limit is
not a solution of the conjecture.

## Evidence

The independently recomputed literal recursion, with one branch per nonempty
labelled subset and immediate stopping at zero, gives `a(0..3)=1,1,13,5419`.
These are smoke values, not evidence for the limit. The limit is carried by
the Lean theorem and its axiom closure; no external-problem KPI is attached
before independent review and actual dev delivery.

## Triage

Tier 1: the full source assertion is the formal theorem. Repository settlement
and delivery remain separate from the proof.

### What the settlement would show

The internal-word representation and uniform factorial-scale estimates
identify the diagonal root constant `1/log(2)`. No neighbouring limit or
fixed-dimension endpoint formula is added as a separate deliverable.

## ASSUMED-UNVERIFIED

Worldwide priority and completeness of the literature search remain
unverified. The live revision 24 supersedes cached search snippets that still
show the historical conjecture. Its stronger signed assertion has not been
verified as an existing proved result; neither first-proof priority nor a
numerical-fit origin is asserted. No new resolved-problem KPI is claimed.

The reported primary-source reading covers GHOW1990's author PDF,
DOI [10.1007/BF01787724](https://doi.org/10.1007/BF01787724), pages 133–146.
Its endpoint asymptotic fixes `k` and has error `O_k`; it does not directly
supply the growing-dimension first-zero theorem. Caughman2011's author text,
DOI [10.1016/j.disc.2011.04.024](https://doi.org/10.1016/j.disc.2011.04.024),
was also read: its exact endpoint formulas allow arbitrary finite dimension.
They must not all be labelled fixed-dimension results. The required uniform
first-zero diagonal theorem was not found in the searched scope.

[A262810 revision 19](https://oeis.org/A262810) already asserts Kotesovec's
2016 asymptotic for height and dimension both equal to `n`; it is not a
fixed-dimension assertion. Its public history #12, March 23, 2016, was read;
#13 is approval, not a proof. Targeted reading of author papers, notes and
history did not locate a proof source. The transfer
`log I(n,n-1) - log b(n) = o(n^2)`, with `b(n)=A262810(n)`, was not found in
that literature scope either. Neither gap requires replacing or reproving
the existing full Lean proof. The stronger A263160 revision 24 assertion is
a more direct source lead, with its proof, constant and error control still
unverified. Source response identities and the historical pins are recorded
in the corresponding Library note.
