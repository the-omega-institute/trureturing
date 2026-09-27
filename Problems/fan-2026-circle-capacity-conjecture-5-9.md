---
slug: fan-2026-circle-capacity-conjecture-5-9
bibkey: fan2026riesz
doi: 10.48550/arXiv.2609.11186
url: https://arxiv.org/abs/2609.11186v1
triage: theorem
motivation_gids:
  - D5/S3/Geometry/Distances/FanCircleCapacity.result
---

# Fan Conjecture 5.9: moving three-point circle capacity

## Problem

Conjecture 5.9 of Qiuling Fan, *Riesz capacity ratios with negative
exponents*, arXiv:2609.11186v1, printed page 19, states:

> Suppose r ≥ 2. Let A, B, C be three points on the unit circle. Fix B and C
> such that they are symmetric with respect to the x-axis, having polar angles
> φ and −φ, respectively, where φ ∈ (π/2, 2π/3]. Move A along the
> circle with polar angle ψ ∈ [0, 2π − 3φ], so that BC remains the
> longest side of the triangle △ABC. Then the capacity of the three-point set
> {A, B, C} is maximized when ψ = 2π − 3φ, i.e., when AC = BC.

The formal target keeps that original domain exactly. For every real `r >= 2`,
`pi/2 < phi <= 2*pi/3`, and `0 <= psi <= 2*pi-3*phi`, it compares the set of
actual complex unit-circle points at angles `psi`, `phi`, and `-phi` with the
isosceles endpoint. Capacity is Fan's negative-exponent Riesz capacity: the
`1/r` power of the supremum of the positive `r`-power distance energy over all
probability measures on the actual point subtype. The target does not restrict
`r` to integers, impose positive singleton masses, use a finite grid, or claim
strictness or uniqueness.

## Motivation

The frozen declaration
`D5/S3/Geometry/Distances/FanCircleCapacity.result` is the exact formal
settlement whose source identity this dossier records. The moving point is
constrained by a fixed circle and a fixed longest chord; this is not the
unconstrained three-point optimizer or a capacity-ratio problem. The endpoint
comparison also crosses a change of optimizer support, so a proof must handle
the zero-mass branch rather than silently assume three positive masses.

## Gap

Fan's Section 5.4.1 records an unsuccessful monotonicity approach, not a proof
of Conjecture 5.9. Clark and Laugesen, *Maximizing Riesz Capacity Ratios:
Conjectures and Theorems*, Theorem 8, supply the classical exact energy maximum
for a three-point metric space, and their Section 7 supplies the concave-power
argument used below. Those results do not state the fixed-circle,
fixed-longest-chord comparison in Conjecture 5.9. The remaining gap is to bind
the optimizer to all probability measures on the actual point subtype and
prove that its attained value is nondecreasing along Fan's prescribed motion,
including the support transition.

## Route

For a moving angle `t`, set `x=(phi-t)/2` and `y=(phi+t)/2`. The source bounds
give `0<x<=y<=pi-phi<=pi/2` and `x+y=phi`. The three chord lengths are
`a=2*sin(x)`, `b=2*sin(y)`, and the constant `c=2*sin(phi)`, with
`0<a<=b<=c`. Write `A=a^r`, `B=b^r`, `C=c^r`, and `s=A+B-C`.

First transport a probability measure on the actual three-point subtype to an
ambient measure concentrated on that set, and transport it back. Finite
integration then expresses its energy through the singleton masses `u,v,w` on
the closed simplex, including zero masses, as
`2*C*u*v + 2*A*v*w + 2*B*w*u`. If `s<=0`, its maximum is `C/2`, attained at
`(1/2,1/2,0)`. If `s>0`, put `D=4*A*B-s^2`; the nonnegative masses

`u0=A*(B+C-A)/D`, `v0=B*(C+A-B)/D`, and `w0=C*(A+B-C)/D`

sum to one and attain `U=2*A*B*C/D`. The completed-square identity

`U-energy = ((2*B*(u-u0)+s*(v-v0))^2 + D*(v-v0)^2)/(2*B)`

proves the upper bound. Thus both branches are the single attained profile

`U=(C/2)*(4*A*B)/(4*A*B-max(s,0)^2)`.

On the active branch, apply the Clark-Laugesen concave-power inequality
`v-u <= v^p-u^p` for `p>=1`, `0<=u<=v<=1`, and `u^p+v^p>=1`, with
`p=r/2`, `u=a^2/c^2`, and `v=b^2/c^2`. Together with the chord and cotangent
identities, it makes
`(B+C-A)*cot(y)-(A+C-B)*cot(x)` nonnegative. Differentiating the unified
profile gives a nonnegative derivative when `s>0`, zero when `s<0`, and zero
at `s=0` because `max(s,0)^2` is differentiable there. Continuity and the
mean-value theorem make the attained energy nondecreasing on the whole
interval. The increasing `1/r` power preserves the endpoint comparison, and
at `t=2*pi-3*phi` one has `b=c`, exactly Fan's isosceles endpoint.

## Falsifier

A probability measure on the actual point subtype whose energy exceeds the
displayed optimizer, a failure of the ambient/subtype transport, a point in the
stated real parameter domain where the attained energy decreases, or a mismatch
between the formal endpoint and `psi=2*pi-3*phi` would invalidate the route or
settlement. A finite-grid computation, an integer-exponent theorem, or a proof
for positive singleton masses only would not settle the registered problem.
A prior proof of the same fully quantified source statement would invalidate
open-problem-resolution eligibility without changing the theorem's truth.

## Evidence

The primary arXiv v1 definitions, Conjecture 5.9, and Section 5.4.1 were read at
the versioned source recorded by `D5/L/Geometry/fan2026riesz`. The same Library
note records the actual probability-measure convention, the exact parameter
range, and the source's unsuccessful approach. The preregistration is issue
#9471 and quotes the source statement before the candidate proof work.

The bounded prior-work comparison covered Fan's 2025 thesis, the relevant
arXiv v1 paper sections, Clark-Laugesen Theorem 8 and Section 7, the final SIAM
version of that paper, Fan's pinned source repository, and the differently
constrained triangle work identified in issue #9471. Clark-Laugesen receive
credit for the three-point optimizer and concave-power step. The subtype
measure equivalence, explicit attainment on the full closed simplex, unified
support-transition profile, and fixed-circle derivative comparison are the
repository route. The frozen result retains only `propext`,
`Classical.choice`, and `Quot.sound` in its axiom closure.

## Triage

First tier: a named conjecture in a 2026 paper, preregistered in issue #9471.
`admission_basis: open-problem-resolution`; `proof_shape: content` for the
single public `result`. Its live proof contains the full measure bridge,
attained optimizer, and monotonicity argument rather than only instantiating an
existing fixed-circle theorem. The three public definitions are the necessary
source objects, and no bind-only companion theorem is delivered. The result is
uniform in all real parameters in the source domain, not bounded enumeration,
a checker, numeric reduction, or a certified finite instance; `utility: none`.

## ASSUMED-UNVERIFIED

The prior-resolution finding is bounded to the sources and repository searches
recorded in issue #9471 and the Library note. It is not an exhaustive worldwide
novelty, priority, or independent-proof claim. The final metadata still
requires independent review and CI; this dossier does not claim merge, issue
closure, programme completion, or KPI credit. Fan's other conjectures,
capacity-ratio optimizations, strictness, uniqueness, and equality
classification are outside this result.
