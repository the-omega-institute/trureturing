---
slug: ghosh-birbonshi-ojha-2026-weighted-shift-root-uniqueness
bibkey: ghoshbirbonshiojha2026weightedshift
doi: null
url: https://arxiv.org/abs/2608.17486v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/RealRootedCoefficientNewton
---

# Ghosh, Birbonshi and Ojha: the unique polynomial root

## Problem

Section 2, Open question 1 of arXiv:2608.17486v1 asks:

> For $s,t>0$ and $0<q<1$ does the polynomial $g(z)$ defined in \eqref{g(z)} have a unique root in $(\frac{1}{3},1)$?

The exact public definitions and result are:

```lean
def g (s t q z : ℝ) : ℝ :=
  t*q^7*z^8 + q^6*(t*q-1)*z^7 + 3*q^5*(q-s)*z^6 + 5*q^4*(s*q-1)*z^5 +
  q^3*(7*q-9*t)*z^4 + 7*q^2*(t*q-1)*z^3 + 5*q*(q-s)*z^2 + 3*(s*q-1)*z + 1

theorem result (s t q : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hq : 0 < q) (hq1 : q < 1) :
    ∃! z : ℝ, (1 / 3 : ℝ) < z ∧ z < 1 ∧ g s t q z = 0
```

All four variables are real. Positivity of s and t and the strict bounds
on q are the only parameter hypotheses. The conclusion includes both
existence and uniqueness with strict interval bounds. There is no relation
between s and t and no compact restriction on their values.

## Motivation

The unrestricted scalar question is preregistered in
https://github.com/the-omega-institute/trureturing/issues/14349.
This is a recent explicit external question in the first problem tier.
The scalar real-polynomial domain also contains the Newton inequality
module named in the motivation address; that module is context and is
neither a dependency nor a premise of the root theorem.

## Gap

The source gives a restricted uniqueness theorem and an s=t reduction,
then explicitly asks the full question. The bounded literature readings
and unread predecessor boundary are recorded in the source note
[ghoshbirbonshiojha2026weightedshift](../Library/Analytic/ghoshbirbonshiojha2026weightedshift.md).
The exact scalar assertion is the subject of the Lean result. No claim
about the numerical radius of the infinite weighted shift is made.

## Route

The endpoint evaluations satisfy g(1/3)>0 and g(1)<0. The intermediate
value theorem therefore supplies a root strictly inside the interval.
For such z set A=sqz, c=q²z², B=tq³z³, P=1+A+c+B and b=z².
Then A,B,P>0 and 0<c<b<1. Write

$$
J(z,c)=(z^2-6z-3)c^3+(15z^2-18z-21)c^2
 +(63z^2-90z+35)c+81z^2-78z+21.
$$

With α₃=z²−6z−3 and α₂=15z²−18z−21, the exact identities are

$$
\begin{aligned}
J(z,0)&=81(z-13/27)^2+20/9,\\
J(z,b)&=(1-z)^3\bigl(6+15(1-z)+8z^2+z^4(3-z)\bigr),\\
bJ(z,c)&=(b-c)J(z,0)+cJ(z,b)
 +bc(b-c)\bigl(-\alpha_2-\alpha_3(b+c)\bigr).
\end{aligned}
$$

Both α₂ and α₃ are negative. The endpoint values are strictly positive,
and the chord identity yields J(z,c)>0. For the polynomial derivative g′,

$$
\begin{aligned}
&2z(1-z)(3+c)g'(z)+PJ(z,c)
 +8A(1-z)^2(1-c^2)(3-c)\\
&\qquad=\bigl((7-11z)(3+c)+4c(1-z)\bigr)g(z).
\end{aligned}
$$

At a zero every additional term on the left is strictly positive, so
its derivative is strictly negative. Between two alleged ordered roots
u<v, Mathlib's differential fence with boundary zero gives g≤0.
The local sign theorem at v gives g>0 just to its left, a contradiction.

The proof directly applies pinned Mathlib's
`intermediate_value_Icc'`, `image_le_of_deriv_right_lt_deriv_boundary`
and `eventually_nhdsWithin_sign_eq_of_deriv_neg` inside the single result.
The last theorem has an ordinary neighborhood conclusion despite its name.
All polynomial identities, inequalities and interval facts are local;
there is no named algebra helper or generic uniqueness wrapper.

## Falsifier

An admissible real triple s,t,q with zero or multiple roots in the specified
open interval would refute the source assertion. A failed certificate
identity or a missing strict sign within the stated domain would invalidate
this proof route. A sampled numerical approximation proves neither case.

## Evidence

`D5/S3/Analytic/GhoshWeightedShiftRootUniqueness.result` compiles with
axioms propext, Classical.choice and Quot.sound only. Its proof shape
is bind-only: the polynomial identities and sign estimates are obtained
by normalization, followed by direct applications of the existing
analytic results. The proposed admission basis is open-problem-resolution
for the exact preregistered external question; no escape witness is asserted.

## Triage

The module has computational_content.kind=none. It is an exact theorem
for all admissible real parameters, rather than bounded enumeration,
a checker, a numerical reduction or a certified finite instance.

### What the settlement shows

**PROVED — exact scalar scope.** The existing checked result
`D5/S3/Analytic/GhoshWeightedShiftRootUniqueness.result` proves that for
every real $s,t>0$ and $0<q<1$ the full polynomial above has exactly one
real zero in $(1/3,1)$. This answers Section 2, Open question 1
affirmatively, including parameters outside the source's Case 1
$s,t\in(q,1/q)$ and without requiring $s=t$. The Case 1 restriction is
therefore unnecessary for this scalar interval-root assertion.

**PROVED — local downward crossing.** In the proof of that same result,
the positive certificate $J(z,c)$ and the derivative identity in
[Route](#route) force $g'(z)<0$ at every zero in $(1/3,1)$.
The decisive mechanism is strict downward crossing at zeros: the
differential fence between two alleged zeros conflicts with the positive
sign just to the left of the later zero. Endpoint signs supply existence.
This is a root-local derivative estimate; global monotonicity on the
interval is not asserted. These are steps of the existing proof, not
additional delivered theorems.

**OPEN — extensions and sharpness.** Relaxing $s>0$ or $t>0$ to allow
zero or negative parameters, allowing $q=0$, $q=1$ or $q$ outside $(0,1)$,
and the sharpness of the interval endpoints remain unverified here.
Other real or complex roots, roots outside $(1/3,1)$, and neighbouring
polynomial or parameter-dependence questions are also OPEN. The checked
result does not settle these extensions or prove endpoint optimality.

**OPEN — optimization and operator bridge.** The source's Section 2
relates roots of $g$ to critical points of its lower-bound function $f$;
the scalar result supplies the previously unresolved uniqueness in
$(1/3,1)$ for unrestricted admissible parameters. A formal bridge from
this fact to the supremum of $f$ on $(0,1)$ and to a lower bound for the
operator numerical radius remains unformalized and OPEN, including the
source's separate exclusion of roots below $1/3$. No optimality of that
bound is proved here. Section 3's entire function $F_T$, its least
positive root, and its identification with the exact numerical radius
are separate unformalized operator conclusions and remain OPEN here.
No further extension or neighbouring result is claimed from this
settlement.

## ASSUMED-UNVERIFIED

The predecessor full text remains unread, and the literature absence
finding is limited to the stated search scope. Independent implementation
review, canonical freezing, required CI and merge remain publication
obligations. The resolution claim requires the canonical frozen declaration
before final content admission. Information escape registration
is suspended under the current repository rule.
