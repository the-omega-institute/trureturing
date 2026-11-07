---
slug: occil-convex-bernstein-corrections
bibkey: occil2026bernreq
doi: null
url: https://peteroupc.github.io/bernreq.html#Other_Questions
triage: theorem
motivation_gids:
  - D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.result
---

# Both convex Bernstein correction prescriptions fail

## Problem

Peter Occil, *Open Questions on the Bernoulli Factory Problem*, “Other Questions”,
first item after the final “Prove or disprove”, asks:

> Given that $f:[0,1]\to (0,1]$ is convex, the polynomials $(g_n) = (B_n(f) - \max\lbrace\text{abs}(B_n(f)(\lambda)-f(\lambda))) : 0\le\lambda\le 1\rbrace$ (where $n$ is a positive integer power of 2) are in Bernstein form of degree $n$, converge to $f$ from below, and satisfy: $(g_{2n}-g_{n})$ is a polynomial with nonnegative Bernstein coefficients once it's rewritten to a polynomial in Bernstein form of degree exactly $2n$. The same is true for the polynomials $(g_n) = (B_n(f) - \text{abs}(B_n(f)(1/2)-f(1/2)))$, if $f$ is also symmetric about 1/2.

The [Library source note](../Library/Analytic/occil2026bernreq.md) pins the
original text and basis convention. The unchanged coefficient conjunction,
its exact quantifiers and strict preregistration are
[issue #27489](https://github.com/the-omega-institute/trureturing/issues/27489#issuecomment-6698804052).
This is an author-published Tier 1 question, with first publication unknown.
The source is pinned to [ec9ea9783cd27a7169f0bf3e3e344286f14babe3](https://github.com/peteroupc/peteroupc.github.io/blob/ec9ea9783cd27a7169f0bf3e3e344286f14babe3/bernreq.md).
The source assertion is verified; global literature completeness and publication priority are not established.

## Motivation

A nonnegative polynomial on the interval need not have nonnegative Bernstein
coefficients at a fixed representation degree. The source's coefficient
monotonicity is stronger than pointwise monotonicity of lower approximants.

## Gap

The formal target is the full registered universal coefficient conjunction.
All functions and scalars are real, and every coefficient index is included.
The operator uses the original samples $f(j/n)$ and the normalized basis
$\binom njX^j(1-X)^{n-j}$. The two branches quantify over $n=2^k$,
$k\ge1$, and require representation degree exactly $2n$.
The maximum-error branch quantifies over actual attained maxima at both
scales; the midpoint branch quantifies over symmetric functions without a
maximum premise. No continuity assumption is introduced. The result refutes
the coefficient requirement in each original branch; it does not require
choosing a convergence topology or disproving convergence separately.

## Route

Take $f(x)=x^2-x+1/2=(x-1/2)^2+1/4$ and $n=2=2^1$.
Its values lie in $(0,1]$ on $[0,1]$, it is convex, and $f(1-x)=f(x)$.
The native proof checks the convexity inequality for every permitted pair
and weight. Direct polynomial identities give

$$
B_2f(X)=	frac12(X^2-X)+	frac12,\qquad
B_4f(X)=	frac34(X^2-X)+	frac12.
$$

For every $x\in[0,1]$, the two errors are $x(1-x)/2$ and $x(1-x)/4$.
Their actual maxima, attained at $x=1/2$, are $1/8$ and $1/16$.
These are also the two midpoint absolute errors. Thus both prescriptions
have the identical increment

$$
p(X)=	frac1{16}-	frac14X(1-X)
     =	frac14(X-1/2)^2.
$$

Its exact degree-4 normalized Bernstein representation is

$$
p(X)=\sum_{j=0}^4 c_j\binom4jX^j(1-X)^{4-j},\qquad
(c_0,c_1,c_2,c_3,c_4)=(1/16,0,-1/48,0,1/16).
$$

The real coefficient vector is unique: map a competing polynomial identity
to complex coefficients, apply the existing complex Bernstein independence
theorem, and use injectivity of the real embedding. Hence no competing
nonnegative coefficient representation exists.

## Falsifier

A different sample operator, unnormalized basis, representation degree,
correction term, domain or maximum interpretation would answer a different
question. Every one of these is explicit in the native definitions. The
proof uses identities for all real inputs and interval-wide inequalities,
not numerical samples or finite positivity testing.

## Evidence

The source is
[OccilBernsteinCorrectionRefutation.lean](../D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.lean),
with its [mathematical exposition](../Blueprint/D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.md).
`claim : Prop` is the conjunction of the universal maximum and midpoint
branches; the sole public theorem `result : Not claim` is its literal negation.
The private consumed `branch_refutations` proves the negation of each
universal branch independently. The public proof uses the maximum component
to negate the conjunction; the private conjunction also checks the midpoint
failure, with its own symmetry and exact midpoint-error substitutions.
`nonnegativeCoefficients` asks for a nonnegative normalized representation;
`realization_unique` identifies every such representation with the displayed vector.
The existing frozen `CommonDenominatorPolynomialBasis.bernstein_linearIndependent_complex`
is applied through the injective real embedding, rather than reproved.

All thirteen authored theorems are bind-only under the repository's
proof-shape rule. The twelve private helpers have actual live consumers;
they supply no new escape witness. Admission is the designated external
`open-problem-resolution` for the unchanged question in #27489, with
resolution kind `Refuted`. The sole public theorem is the designated literal
refutation result and is exempt from four-slot escape registration.
Its axiom closure, and those of all twelve helpers, are contained in
$\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.

The current canonical frozen identity is recorded in
[the module state](../Golden/Frozen/state/D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.lean.json).
Its module statement identity is `sha256:fe4838383ce940e860456b023f80f63ea502d4e664df7814a82d0d2f6ecd2c07`.
The exact declaration statement identities are:

- `claim`: `sha256:348705f12418a84b09642bab72a00cd300486fb4c668f039a2ee0ba4ab5bd949`.
- `result`: `sha256:7e65d33d337aecf79a768b4d7f4a579869edbe9634a1dc676dafb098623ecb19`.
- Private `branch_refutations`: `sha256:f1e4363019756fa333c95416678f80394f882394b32633c4c151f8226790589b`.

## Triage

1. **Proved in Lean:** both full universal coefficient assertions are false.
   The same admissible convex symmetric quadratic, at $n=2$, has coefficient
   $-1/48$ in each prescribed degree-4 increment. This refutes each original
   conjunction through its coefficient clause; no convergence topology is
   substituted for the source's unspecified one.
2. **Proved in Lean:** the exact sample-polynomial identities, interval-wide
   errors, actual maxima with midpoint attainers, normalized coefficient
   representation and representation uniqueness support that refutation.
   These are private consumed facts, not additional public settlement claims.
3. **Surviving mathematical statements:** the displayed increment
   $(X-1/2)^2/4$ is pointwise nonnegative. At the witnessed scales, the
   displayed identities give $g_2=f-(X-1/2)^2/2$ and
   $g_4=f-(X-1/2)^2/4$, so $g_2\le g_4\le f$ on the interval.
   These are elementary consequences of the checked identities, not new
   separately frozen declarations. They exhibit the precise separation
   between pointwise ordering and the demanded coefficient ordering.
4. **Computed evidence:** no numerical experiment or sample-based positivity
   test is used as settlement evidence. The rational values in Route are
   exact identities checked in the Lean proof.
5. **Other questions in the source:** the Main Question asks for some suitable
   coefficient-consistent sequence. Two failed fixed prescriptions do not
   refute that existential question, approximate factories, convergence-rate
   constructions, or general Bernoulli-factory existence. The source's
   polynomial-approximation conjecture concerns different operators and
   estimates; this result gives no new settlement of it. Its reported
   external counterexample is a separate source claim, not Lean evidence here.
6. **Coin-flipping degree:** the negative degree-4 coefficient demonstrates
   why an exact representation degree matters. The increment vanishes at
   $1/2$, so it does not satisfy the strict interior positivity assumed in
   that separate source question. No upper bound, sharp degree or settlement
   of that question follows.
7. **Open:** which alternative corrections, stronger hypotheses or other
   approximation sequences satisfy coefficient consistency, and their sharp
   rates and computational costs, are not determined by this module.
   The separate strong-simulability conditions, pushdown-automaton and
   multiple-output questions remain outside this refutation.

## ASSUMED-UNVERIFIED

First publication, exhaustive literature completeness, global originality
and publication priority are unverified. The pinned author source is a
Tier 1 question, not a peer-reviewed theorem. The registration's exact
original first-mathematical-execution time and 240-second compliance are
unavailable and unverified; no retrospective timing or scoring claim is
made. Convergence for all scales, alternative schemes, sharp correction
thresholds, the other source questions and external results mentioned above
are not Lean-verified by this module.
