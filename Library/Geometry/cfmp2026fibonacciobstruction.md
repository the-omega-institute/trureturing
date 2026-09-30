---
title: CFMP Fibonacci observation obstruction
date: 2026-09-30
status: scoped-formal-bridge
---

The cyclic CFMP return observation on integer pairs is
C(x,y) = (2x-y, x+2y). Write J(x,y)=(y,x), F(x,y)=(y,x+y), and
D(x,y)=(-x+2y, 2x+y). The identities
D^2=5I, C=D∘J, and C∘JFJ=F∘C
identify the return readout with the golden discriminant after a coordinate
swap and show that the Fibonacci evolution preserves observation fibres.

For k,t in N, set s(k,t)=(kt,2kt). Then C(z+s(k,t)) differs from C(z)
by (0,5kt), so both coordinates are congruent modulo 5k. For positive k,
the exact integer kernel is characterized by
x=kt and y=2kt+5ks; the image condition is 2r+s ≡ 0 (mod 5).
The Lean declarations are in
D5.S3.Geometry.Hyperideal.FibonacciObservation, with the statement-level
Blueprint at Blueprint/D5/S3/Geometry/Hyperideal/FibonacciObservation.md.

At the concrete modulus 5040 = 5 * 1008, the same congruence obstruction
persists. This records the factor-five component only; it is not a bridge to
Robin's criterion or RH, and it makes no claim about an additional factor-seven
phase.

Scope: this is an algebraic obstruction for framed return parameters. It does not
claim five distinct unmarked manifolds, a general hyperbolic realization, or a
solution of the minimum-six CFMP problem. The geometric Sections 133–139 remain
written context and are not imported as formal premises.
