---
bibkey: planatsole2026secondlevel
authors: Michel Planat and Patrick Solé
year: 2026
title: Second-Level Concavity of the Riemann Xi Kernel
doi: null
url: https://arxiv.org/abs/2608.19160v1
claim: Theorem 1.1 states strict log-concavity of the first Laguerre expression for the actual square-variable Riemann theta kernel on the positive half-line.
strata_touched:
  - D5/S3/Zeros/Jensen/SourceThetaMomentBounds
  - D5/S3/Analytic/Fourier/XiThetaTransform
license: citation-only
triage: anchor
---

# Second-level concavity of the actual theta kernel

The pinned preprint uses Csordas' normalization, denoted here by $K$ to
distinguish it from the repository's Romik kernel:

$$
K(u)=\sum_{m\ge1}\pi m^2(2\pi m^2e^{4u}-3)
                 e^{5u-\pi m^2e^{4u}}.
$$

Equation (1.2) sets $s(t)=K(\sqrt t)$ and
$f(t)=s'(t)^2-s(t)s''(t)$. Theorem 1.1, printed p.1, states

$$
f(t)>0,\qquad (\log f)''(t)<0\qquad(t>0),
$$

where positivity of $f$ is the previously established first-level
square-variable log-concavity. The second inequality addresses the
Csordas–Dimitrov conjecture restated as Csordas Open Problem 4.14.
This preprint-reported result should be reused rather than treated as a
new theorem to discover in the project.

The proof uses a directed-rounding local Taylor certificate near $t=0$.
Its two continuations use, respectively, a first theta summand with
explicit tail bounds and a Jacobi differential/elliptic phase-space
argument. They share the local certificate. Sections 3 and 8 describe
the certificate bounds and supplementary scripts. These are the
preprint's computer-assisted proof claims; the scripts have not been
independently executed here, and no Lean proof of Theorem 1.1 is supplied.

## Correspondence with the fixed repository source

The source formulas in [Romik's kernel note](../Analytic/romik2021orthogonal.md)
give the normalization correspondence

$$
\Phi(x)=2K(x/2),\qquad T=x^2/4,
\qquad S(T)=\Phi(2\sqrt T)=2s(T).
$$

The paper's $t$ is thus the fixed receiving coordinate $T$.
Replacing $T$ by $x^2$ while retaining the same prescribed source
polynomial nodes changes the correspondence and is not an admissible
application of this result.

For $v>0$ and $\xi_0=\xi(1/2)>0$, the density-ratio notation is

$$
r_v(T)=A_ve^{T/v}S(T),\qquad
A_v=2\sqrt{\pi v}/\xi_0.
$$

The elementary transport identity is

$$
r_v'(T)^2-r_v(T)r_v''(T)
=A_v^2e^{2T/v}\bigl(S'(T)^2-S(T)S''(T)\bigr).
$$

The expression on the right is $4A_v^2e^{2T/v}f(T)$, so the source's
second-level conclusion transports as

$$
\frac{d^2}{dT^2}\log\!\bigl(r_v'(T)^2-r_v(T)r_v''(T)\bigr)
=(\log f)''(T)<0\qquad(T>0,\ v>0).
$$

Multiplication by a positive constant and an exponential adds only an
affine term to the logarithm. This is a paper-level application with
the stated coordinate and tilt, not new mathematics or an additional
formalized declaration.

## Unpaid interface to the RH and Robin goals

Theorem 1.1 states a finite-order differential inequality for every
$T>0$. A derivation of all higher derivative inequalities or a weighted
comparison at every prescribed source Jensen node $v=n\lambda$ has not
been established here. The neighboring-row signed estimate, and the
extra vanishing needed at common zeros with correct multiplicities,
remain separate obligations.
The preprint explicitly makes no assertion of RH; this note supplies
no proof of strict Robin for every integer greater than 5040.

The [original-variable derivative counterexample](sra2026thetakernelcounterexample.md)
concerns Csordas Open Problem 4.13, a different assertion. Its negative
witness must not be transferred to $T$ derivatives without a new argument.

The separate proposed cumulative Peano sufficient condition is investigated
in the private experiment repository's
[theta-node interval certificate](https://github.com/the-omega-institute/trureturing-experiments/tree/516e129fbffe660a60a4d9231436c69b573f8f58/experiments/theta-peano-node-obstruction).
That entry contains the source correspondence, analytic truncation bounds,
executable certificate and its result. It tests a stronger condition than
the original neighboring-row estimate and is not a theorem attributed to
this preprint or a Lean proof of the target estimate.

The separate [square-variable derivative-Hankel certificate](https://github.com/the-omega-institute/trureturing-experiments/tree/e02b1d2936b9e3207939677807a76d611025f699/experiments/theta-square-hankel-obstruction)
investigates the stronger full alternating determinant hierarchy for
the actual $S(T)$. It computes $T$ derivatives directly with analytic
remainder bounds, rather than transferring an original-variable
counterexample. The experiment's conclusion concerns that sufficient
hierarchy; it neither changes this preprint's finite-order statement
nor supplies or refutes the original prescribed-node scalar estimate.
