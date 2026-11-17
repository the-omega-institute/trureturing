---
slug: fan-kobayashi-molnar-2026-remark-4-16
bibkey: fankobayashimolnar2025family
doi: 10.1007/s11139-026-01408-3
url: https://arxiv.org/abs/2511.02106v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415
---

# Fan--Kobayashi--Molnar Remark 4.16

## Problem

Fan, Kobayashi and Molnar, *A family of analogues to the Robin criterion*,
Ramanujan Journal 70 (2026), article 40, arXiv:2511.02106v1, write in Remark
4.16:

> It seems that Lemma 4.15 holds for all κ > 1. This would follow if one could show that the function [(x²+2)^κ − 2^κ][(x+1)^κ − 1]² − [(x²+x+1)^κ − (x+1)^κ]² is strictly increasing in x ∈ [0, ∞) and κ ∈ [1, ∞). In fact, monotonicity in either of the two variable suffices.

Their Lemma 4.15 states:

> For any κ ≥ 3/2 and any ϵ > 0, we have x₂ < √(2x).

Issue [#30049](https://github.com/the-omega-institute/trureturing/issues/30049),
Problem A, preregistered the Lean target
`F^{[κ]}(y,2) < F^{[κ]}(y²/2,1)`.

## Motivation

This is a Tier 1 external open problem. The proposed target is the analytic
full implication that removes the source paper's restriction κ ≥ 3/2 in the local
comparison underlying Lemma 4.15. Its settlement is recorded as an
open-problem resolution because the final theorem answers the external assertion; its bind-only
auxiliaries have actual mathematical consumers.

## Gap

The complete arXiv v1 article was checked: Remark 4.16 gives a sufficient
monotonicity route but no proof, and the paper contains no proof of the
all-κ version of Lemma 4.15. Molnar, *Reciprocal LCM powers and Robin's
criterion*, arXiv:2610.12816v1, only restates the κ > 3/2 result in its related
discussion. The arXiv and web searches used for this dossier found no later
answer to Remark 4.16. This is a bounded source check and does not assert
exhaustive worldwide priority.

## Route

For κ > 1 set

$$
C_\kappa(t)=(1+t)^\kappa-t^\kappa,
\qquad
D_\kappa(t)=(1+t)^{\kappa-1}-t^{\kappa-1},
\qquad
B_\kappa(t)=\log C_\kappa(t).
$$

The curvature calculation is

$$
(C_\kappa')^2-C_\kappa C_\kappa''
=\kappa D_\kappa^2+\kappa(\kappa-1)[t(1+t)]^{\kappa-2}.
$$

It gives strict concavity of $B_\kappa$ on $(0,\infty)$, concavity on
$[0,\infty)$, and $B_\kappa(0)=0$. With $s=1/y$ and $h=1/y^2$, the
assumption $y>1$ gives $0<h<s$. Strictly decreasing equal-length increments
of $B_\kappa$ give

$$
B_\kappa(s+h)-B_\kappa(s)<B_\kappa(2h)-B_\kappa(h)
\le \tfrac12 B_\kappa(2h).
$$

Undoing the common powers of $y$ is exactly

$$
[(y^2+2)^\kappa-2^\kappa][(y+1)^\kappa-1]^2
>
[(y^2+y+1)^\kappa-(y+1)^\kappa]^2.
$$

Factoring the relevant cubic and quadratic expressions and using
$0<\log(y^2/2)<2\log y$ for $y>\sqrt2$ yields
$F^{[\kappa]}(y,2)<F^{[\kappa]}(y^2/2,1)$.

For $t>0$ put $r=t/(1+t)$. The elasticity is

$$
\phi(t)=tB_\kappa'(t)
=\kappa\left(1-\frac{1}{(1-r^\kappa)/(1-r)}\right)>0.
$$

Strict convexity of $r^\kappa$ makes the secant slope
$(1-r^\kappa)/(1-r)$ strictly increasing on $(0,1)$, so $\phi$ is
strictly increasing. Consequently $g(s)=B_\kappa(s+s^2)-B_\kappa(s)>0$
for $s>0$, and

$$
s g'(s)=(1+2s)sB_\kappa'(s+s^2)-sB_\kappa'(s)>0,
$$

because $(s+s^2)B_\kappa'(s+s^2)>sB_\kappa'(s)$ and
$s^2B_\kappa'(s+s^2)>0$. Thus $g$ is strictly increasing.
The factorization gives $F^{[\kappa]}(x,2)=g(1/x)/(\kappa\log x)$:
the positive numerator strictly decreases and the positive denominator
increases for $x>1$. Hence $F^{[\kappa]}(\cdot,2)$ is strictly decreasing.

For any $x,x'>1$ satisfying $F^{[\kappa]}(x',2)=F^{[\kappa]}(x,1)$,
put $y=\sqrt{2x}>\sqrt2$. The comparison gives
$F^{[\kappa]}(y,2)<F^{[\kappa]}(x',2)$; strict decrease implies $x'<y$.
In the paper $x=x_1^{[\kappa]}(\epsilon)$ and
$x'=x_2^{[\kappa]}(\epsilon)$ satisfy this equation. This proves the
full Lemma 4.15 for every $\kappa>1$ without the source Theorem 4.3.

## Falsifier

A real κ > 1 and y > 1 violating the displayed power inequality would
refute the core settlement. A real κ > 1 and y > √2 violating the displayed
$F^{[\kappa]}$ comparison would refute its function form. A mismatch between
the formal $F^{[\kappa]}$ definition and Definition 4.2 of the source paper
would invalidate the source-to-Lean correspondence.

## Evidence

The frozen Lean source is
`D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lean`. The relevant GIDs are:

- `D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415`, proving
  $x'<\sqrt{2x}$ whenever κ > 1, x,x' > 1 and
  $F^{[\kappa]}(x',2)=F^{[\kappa]}(x,1)$;
- `D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415_core`, proving
  the power inequality for every real κ > 1 and y > 1;
- `D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415_F`, proving
  $F^{[\kappa]}(y,2)<F^{[\kappa]}(y^2/2,1)$ for every real κ > 1 and y > √2;
- `D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.logPowerDifference_concavity`,
  supplying the strict logarithmic concavity route.

The existing literature note is
`Library/ArithSums/fankobayashimolnar2025family.md`, with bibkey
`fankobayashimolnar2025family`, DOI `10.1007/s11139-026-01408-3`, and the
pinned arXiv URL. The Scribe resolution edge binds the Problem slug to
`lemma415` with resolution kind `proved`.

## Triage

### Lean proved

1. The power inequality (1.3) holds for κ > 1 and y > 1.
2. The $F^{[\kappa]}$ comparison holds for κ > 1 and y > √2.
3. Elasticity is strictly increasing, as is the positive increment $g$;
   $F^{[\kappa]}(\cdot,2)$ is strictly decreasing on $(1,\infty)$.
4. The complete Lemma 4.15 implication holds for all κ > 1. It applies
   to all solutions of the defining F equation and does not use Theorem 4.3.

### Mathematical derivation not formalized

The existence and inverse-function construction of the source symbols
$x_1^{[\kappa]}(\epsilon)$ and $x_2^{[\kappa]}(\epsilon)$ are not
reconstructed. The theorem instead applies to every pair satisfying their
F equation. The two-variable monotonicity proposed in Remark 4.16 is not
needed and is not asserted.

### Undecided

This settlement does not extend the source Theorem 6.1 to κ ≤ 3/2. The theory
volume's Theorem 1.5 records that for 1 < κ < 3/2 such an extension is
equivalent to RH being false, while the endpoint κ = 3/2 remains undecided.

The source Lemma 4.15 is used there in Lemma 4.30 and Theorem 6.1. Resolving
Remark 4.16 changes the parameter range of that local lemma; it does not
settle the later Robin criterion.

## ASSUMED-UNVERIFIED

The literature statement is limited to the inspected Fan--Kobayashi--Molnar
arXiv v1 and the cited Molnar arXiv v1. The search did not establish an
exhaustive survey of unpublished work, later versions, or all web-indexed
material. The Lean declarations include the full Lemma 4.15 implication. The
interpretation of the later Robin criterion remains outside these declarations.
