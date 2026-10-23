---
bibkey: manzurnoor2026hardyoperator
authors: Juan Manzur; Waleed Noor
year: 2026
title: A Hardy space operator acting on zeta-zeros
doi: null
url: https://arxiv.org/abs/2610.03568v1
claim: The note constructs a bounded Hardy-space operator whose invariance on the closed Nyman--Beurling span is equivalent to RH, with a quantitative distance obstruction for an off-line zero; it does not prove the required invariance.
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
integers $k\ge2$, and write $\overline{\mathcal N}$ for its closure in $H^2$.
For each nonzero real $\tau$, the source constructs a
bounded invertible operator $T_\tau$ on $H^2$ whose adjoint transports the
reproducing kernel $k_s$ to a scalar multiple of $k_{s-i\tau}$.

Theorem 5.1 states the equivalence

$$
 RH
 \iff \overline{\mathcal N}\text{ is }T_\tau\text{-invariant}
 \iff T_\tau h_k\in\overline{\mathcal N}\text{ for some }k\ge2.
$$

If $\rho$ is a zero with $\Re\rho>1/2$ and $\zeta(\rho-i\tau)\ne0$,
the source gives an explicit positive lower bound for
$\operatorname{dist}(T_\tau h_k,\overline{\mathcal N})$. The contradiction under
invariance is an infinite vertical progression of zeros, excluded by a
zero-density estimate.

## Finite-order obstruction for a direct FIB identification

The FIB composition operator

$$
C=MJ=\begin{pmatrix}0&-1\\1&0\end{pmatrix}
$$

has $C^4=I$. The Hardy operator in the source has, with
$\Delta=I-S^*$,

$$
\Delta T_\tau=D_\tau\Delta,\qquad
D_\tau e_j=(j+1)^{i\tau}e_j.
$$

For $\tau\ne0$, $T_\tau$ has no finite period. Indeed, if
$T_\tau^m=I$ for a positive integer $m$, then
$D_{m\tau}\Delta=\Delta$. Applying this to $e_1$ and $e_2$ gives

$$
2^{im\tau}=1,\qquad 3^{im\tau}=1.
$$

If $m\tau\ne0$, these equalities make $\log 2/\log 3$ rational, which
would imply an impossible equality of powers of $2$ and $3$. Hence
$m\tau=0$, a contradiction. Consequently no nonzero-$\tau$ $T_\tau$ can
be the image of $C$ under a surjective intertwiner or a unitary
equivalence. This does not rule out a proper invariant-subspace model;
such a model would be a separate construction and proof obligation.

## Boundary for the FIB route

This result is a sharp example of a dynamical closure condition whose failure
would expose an off-line zero. It does not identify the Hardy operator with
the FIB affine generator $M$, the conjugation $J$, or the four-phase operator
$C=MJ$. A proposed FIB operator model would have to specify the Hilbert space,
the embedding of the Nyman--Beurling generators, and the exact intertwining
identity before this criterion could be transported. The current FIB affine
geometry supplies none of those analytic bridges, so no RH conclusion follows
from the shared words “invariant” or “recursive”.
