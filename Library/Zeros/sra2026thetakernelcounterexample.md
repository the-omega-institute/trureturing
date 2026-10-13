---
bibkey: sra2026thetakernelcounterexample
authors: Count ex Machina (Suvrit Sra)
year: 2026
title: GPT, the Counterexample Machine
doi: null
url: https://arxiv.org/abs/2608.29595v1
claim: Theorem 5.2 reports a computer-assisted negative witness at derivative order nine and argument 1/50 for the actual Jacobi theta kernel's derivative Laguerre inequality.
strata_touched:
  - D5/S3/Zeros/Jensen/SourceThetaMomentBounds
  - D5/S3/Analytic/Fourier/XiThetaTransform
license: citation-only
triage: anchor
---

# A reported counterexample to the original-variable derivative conjecture

Section 5, printed pp.8–9 of the pinned preprint, addresses the
Coffey–Csordas conjecture restated as Csordas Open Problem 4.13.
For the actual kernel

$$
K(u)=\sum_{m\ge1}\pi m^2(2\pi m^2e^{4u}-3)
                 e^{5u-\pi m^2e^{4u}},
$$

the conjecture asks for

$$
J_n^K(u):=K^{(n)}(u)^2-K^{(n-1)}(u)K^{(n+1)}(u)>0
\qquad(n\ge1,\ u\in\mathbb R).
$$

Theorem 5.2 states $J_9^K(1/50)<0$. The reported certificate uses
integer derivative polynomials, outward-rounded interval summation
and an explicit bound for the omitted theta tail. The paper identifies
its [source repository](https://github.com/suvrit/count-ex-machina),
including a high-precision evaluator and a Sage interval certificate.
This note records the source's computer-assisted result; it neither
reruns that certificate nor supplies a new Lean refutation.

The source reports this witness as a refutation of the universal
conjecture. Its certificate and original-variable scope must be retained
in any application. Remark 5.3 does not claim verification of the entire
range $n\le8$.

## Source normalization and limits of transfer

The [repository's original kernel](../Analytic/romik2021orthogonal.md) has
$\Phi(x)=2K(x/2)$. The chain rule gives the paper-level transport

$$
J_n^\Phi(x)=2^{2-2n}J_n^K(x/2).
$$

Thus the source's witness corresponds to $J_9^\Phi(1/25)<0$ under
the repository normalization. This is the actual theta source, rather
than an example obtained by dropping an admissible-kernel tail condition.
The scaling formula is elementary reuse, not a new counterexample.

The square-variable kernel is instead $S(T)=\Phi(2\sqrt T)$,
with $T=x^2/4$. Its derivatives mix original-variable derivatives;
the density ratio $r_v(T)=A_ve^{T/v}S(T)$ introduces a further tilt.
The reported witness consequently supplies no negative witness for
the corresponding $T$-derivative expressions or the signed estimate at
the actual polynomial nodes. It refutes neither RH nor Robin.

The [second-level square-variable concavity theorem](planatsole2026secondlevel.md)
addresses Csordas Open Problem 4.14. These two source results must be
kept separate: a positive result for the square-variable first Laguerre
expression does not assert all-order positivity for original-variable
derivatives.
