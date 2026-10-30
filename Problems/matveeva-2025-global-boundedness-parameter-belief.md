---
slug: matveeva-2025-global-boundedness-parameter-belief
bibkey: matveeva2025precursive
doi: null
url: https://arxiv.org/abs/2511.02121v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/MatveevaGlobalBoundedness.result
---

# Matveeva's literal nonzero-parameter global-boundedness belief

## Problem

Anastasia Matveeva, *On the integrality of some P-recursive sequences*,
arXiv:2511.02121v1, Section 4.2 after the general generating-function
solution of equation (4.1):

> Supposedly, if e does not vanish in the equation above, S(x) is not globally bounded. However, this question remains open for now.

Section 7 states the parameter condition explicitly:

> The case of $b_2 \neq \frac{2a_2b_1-a_1a_2b_0}{a_1}$ is still poorly understood, although we believe it leads to not globally bounded solutions.

The literal assertion quantifies over every rational tuple
$(a_1,a_2,b_0,b_1,b_2)$ with $a_1a_2\neq0$ and
$b_0\notin\{-2,-3,\ldots\}$, and every sequence $s:\mathbb N\to\mathbb Q$
with arbitrary rational initial values satisfying

$$
(n+b_0)s_n+(a_1n+b_1)s_{n-1}+(a_2n+b_2)s_{n-2}=0
\qquad\text{for every }n\geq2.
$$

It asserts that

$$
E=a_1a_2b_0+a_1b_2-2a_2b_1\neq0
\quad\Longrightarrow\quad s\text{ is not globally bounded}.
$$

Definitions 1.4 and 1.5 require both of the following for global
boundedness: a single nonzero integer $C$ for which $C^ns_n$ is an
integer for every $n\geq1$, and a real $R>0$ for which the full complex
series $\sum_{n=0}^{\infty}s_nz^n$ is summable for every complex $z$
with $|z|<R$. The integer witnessing integrality may depend on $n$;
there is no integrality restriction on $s_0$.

There is no minimal-order, nonrationality, normalized-initial-values or
uncancelled-exponential hypothesis. Requiring an exponential factor to
survive simplification of the full generating function would change the
assertion. Conjecture 4.1 is a separate assertion.

## Motivation

`D5/S1/Recurrence/MatveevaGlobalBoundedness.claim` expresses this entire
universal assertion. The sole public theorem
`D5/S1/Recurrence/MatveevaGlobalBoundedness.result` has the literal type
`Not claim`. The counterexample is nonzero and verifies both original
global-boundedness clauses, including actual complex summability.

## Gap

Preregistration [#23051](https://github.com/the-omega-institute/trureturing/issues/23051)
fixes the whole literal event, its quantifiers and tier-1 source scope.
The bounded source and public-solution screening has `prior_art_status:
partial`. The versioned primary contains the quoted open belief. The
screened Bostan publication inventory and Bostan–Salvy–Singer
arXiv:2504.16697v2 passages did not identify a resolution of this parameter
belief; their algebraicity questions do not settle it. MathDB entries
371300 and 371301 concern different assertions, including Conjecture 4.1;
the target's solution count is unknown. Crossref, HAL, DataCite,
MathOverflow, public GitHub and sequence-source searches are bounded
screens. Rate-limited OpenAlex and Semantic Scholar citation inventories
remain unread. These findings establish no worldwide priority or
exhaustive absence of a prior resolution.

## Route

Use the rational sequence $s_n=n+1$ and

$$
(b_0,a_1,b_1,a_2,b_2)=(1,-3,-1,2,1),\qquad E=-5.
$$

The initial values are $s_0=1$ and $s_1=2$. For every $n\geq2$,
the recurrence reduces to the polynomial identity

$$
(n+1)^2+(-3n-1)n+(2n+1)(n-1)=0.
$$

With $C=1$, the integer coefficient is $n+1$ at every positive index.
With $R=1$, the full complex series is summable at every $|z|<1$.
The proof directly applies the pinned Mathlib theorem
`summable_choose_mul_geometric_of_norm_lt_one` with coefficient ring
$\mathbb C$ and parameter $k=1$. Thus the chosen solution satisfies every
premise of `claim` and is globally bounded, contradicting its conclusion.
The argument covers all required indices and the entire open complex
disk, rather than a finite prefix or a formal-series proxy.

## Falsifier

Source correspondence would fail if the claim omitted either
integral scaling or complex convergence, restricted the initial pair,
replaced the parameter condition by persistence of an exponential, or
checked only finitely many recurrence indices. The formal definitions
retain each of these distinctions. A source claim with an additional
minimal-order or nonrationality premise is outside this result.

## Evidence

The Lean source supplies five necessary public definitions, one consumed
private helper and one public result. The per-declaration mathematical
classification is manual `proof_shape: bind-only` throughout:

| Declaration | Role and live consumer |
| --- | --- |
| `integralScaling` | Necessary definition used by `globallyBounded`. |
| `positiveComplexRadius` | Necessary definition used by `globallyBounded`. |
| `globallyBounded` | Necessary definition used by `claim` and `witness_data`. |
| `claim` | Complete external assertion negated by `result`. |
| `witness` | Necessary sequence definition used by `witness_data` and `result`. |
| private `witness_data` | Its recurrence and global-boundedness conjuncts are consumed by `result`; its initial-value conjuncts identify the nonzero source solution. |
| `result` | The sole public conclusion, resolving the preregistered literal assertion. |

The compiler-generated `witness.eq_1` is not an authored companion.
There is no escape witness and no direct frozen D5 dependency.
`admission_basis: open-problem-resolution` uses the whole external
open-problem-resolution exception of CLAUDE.md §3.2, not a claim that
bind-only steps are new intermediate mathematics. The typed Scribe
resolution kind is `Refuted` for this dossier and this result.

The header is `utility: none`: the necessary predicates and their
all-index, all-disk refutation are not a separately delivered finite
checker, enumeration, numerical reduction or certified finite instance.
Arithmetic normalization is subordinate to that infinite symbolic
argument. The accepted proof reuses Mathlib summability directly.
The normal Lean report and canonical freeze own compiled statements,
source bindings and axiom closure; this dossier is not another machine
status or a claim of independent delivery approval.

The source-bound Reg audit is unfinished under
[#23072](https://github.com/the-omega-institute/trureturing/issues/23072).
The faithful attempted registration compiled, but its binding state was
`declared_unresolved`, diagnostic
`IE-C050 ... source.residual_requires_open`, with no binding certificate.
The failed Reg mirror is absent. No `declared_validated` claim is made;
the §3.9 linked-issue boundary does not waive kernel, sorry, axiom,
freeze, Scribe or required checks. Literal negation and `utility: none`
do not themselves exempt this result from registration.

## Triage

### What the settlement shows

Proved by `D5/S1/Recurrence/MatveevaGlobalBoundedness.result`: the entire
literal parameter belief is false. A nonzero value of $E$ does not by
itself exclude a globally bounded rational solution. This is an
existential counterexample to a universal assertion, with neither
initial normalization nor a weakened convergence predicate.

The proof mechanism is an exact polynomial recurrence identity combined
with integer coefficients and an existing complex summability theorem.
It supplies no classification of all $E\neq0$ solutions. Whether
additional minimal-order, nonrationality or exponential-persistence
conditions support another theorem remains open here. Conjecture 4.1
and other source results are not settled or invalidated by this result.

## ASSUMED-UNVERIFIED

Literature priority and exhaustive citation coverage remain unverified.
The Reg binding audit is unfinished as described above. Independent
exact-head delivery reviews, the full actual gate, required CI and later
integration are separate obligations. This result does not certify
those obligations, merge authorization or any solved-problem count.
