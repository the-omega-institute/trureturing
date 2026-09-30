---
title: CFMP Fibonacci observation obstruction
date: 2026-09-30
status: scoped-formal-bridge
---

The cyclic CFMP return observation on integer pairs is
C(x,y) = (2x-y, x+2y). Write J(x,y)=(y,x), F(x,y)=(y,x+y), and
D(x,y)=(-x+2y, 2x+y). The exact identities
D²=5I, C=D∘J, and C∘JFJ=F∘C
show that the return readout is multiplication by the golden discriminant after
a coordinate swap and that this ambiguity persists under the Fibonacci evolution.

For k,t in N, set s(k,t)=(kt,2kt). Then C(z+s(k,t)) differs from C(z)
by (0,5kt). Consequently the two observed coordinates are congruent modulo 5k.
This gives a checkable finite obstruction to recovering framed gluing parameters
from the cyclic return observation alone. The Lean declarations are in
D5.S3.Geometry.Hyperideal.FibonacciObservation, with the statement-level
Blueprint at Blueprint/D5/S3/Geometry/Hyperideal/FibonacciObservation.md.

At the concrete modulus 5040 = 5 * 1008, the same Lean theorem gives the
phase ambiguity. The factor 7 in 5040 = 2^4 * 3^2 * 5 * 7 contributes no
additional kernel state to this return observation, so this is not a bridge to
Robin's criterion or RH.

Scope: this is an algebraic obstruction for framed return parameters. It does not
claim five distinct unmarked manifolds, a general hyperbolic realization, or a
solution of the minimum-six CFMP problem. The written Sections 133–139 and
cfmp_fibonacci_ramification_check.py in PR #9474 provide the geometric families
and finite checks; those checks are supplementary to the Lean identities here.
