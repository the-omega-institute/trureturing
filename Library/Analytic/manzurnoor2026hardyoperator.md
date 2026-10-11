---
bibkey: manzurnoor2026hardyoperator
authors: Juan Manzur; Waleed Noor
year: 2026
title: A Hardy space operator acting on zeta-zeros
doi: null
url: https://arxiv.org/abs/2610.03568v1
claim: The note constructs a bounded Hardy-space operator whose invariance on the Nyman--Beurling span is equivalent to RH, with a quantitative distance obstruction for an off-line zero; it does not prove the required invariance.
strata_touched: []
license: citation-only
triage: anchor
---

# A Hardy-space invariant-subspace criterion

The inspected source is [arXiv:2610.03568v1](https://arxiv.org/abs/2610.03568v1),
submitted 2 October 2026. It works with the standard Hardy-space formulation
of the Báez--Duarte/Nyman--Beurling criterion. The operator construction is a
literature input, not a project formalization or an RH proof.

## The operator and equivalence

Let $\mathcal N$ be the span of the Hardy functions associated with the
integers $k\ge2$. For each nonzero real $\tau$, the source constructs a
bounded invertible operator $T_\tau$ on $H^2$ whose adjoint transports the
reproducing kernel $k_s$ to a scalar multiple of $k_{s-i\tau}$.

Theorem 5.1 states the equivalence

$$
 RH
 \iff \mathcal N\text{ is }T_\tau\text{-invariant}
 \iff T_\tau h_k\in\mathcal N\text{ for some }k\ge2.
$$

If $\rho$ is a zero with $\Re\rho>1/2$ and $\zeta(\rho-i\tau)\ne0$,
the source gives an explicit positive lower bound for
$\operatorname{dist}(T_\tau h_k,\mathcal N)$. The contradiction under
invariance is an infinite vertical progression of zeros, excluded by a
zero-density estimate.

## Boundary for the FIB route

This result is a sharp example of a dynamical closure condition whose failure
would expose an off-line zero. It does not identify the Hardy operator with
the FIB affine generator $M$, the conjugation $J$, or the four-phase operator
$C=MJ$. A proposed FIB operator model would have to specify the Hilbert space,
the embedding of the Nyman--Beurling generators, and the exact intertwining
identity before this criterion could be transported. The current FIB affine
geometry supplies none of those analytic bridges, so no RH conclusion follows
from the shared words “invariant” or “recursive”.
