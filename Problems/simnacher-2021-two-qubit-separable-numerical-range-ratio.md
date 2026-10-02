---
slug: simnacher-2021-two-qubit-separable-numerical-range-ratio
bibkey: simnacher2021separable
doi: 10.1103/PhysRevA.104.042420
url: https://arxiv.org/abs/2107.04365v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.result
---

# The minimal separable numerical range ratio of one two-qubit observable

## Problem

T. Simnacher, J. Czartowski, K. Szymański, K. Życzkowski, *Confident
entanglement detection via the separable numerical range*, Phys. Rev. A 104,
042420 (2021), arXiv:2107.04365v1, Conjecture 8:

> For a single measurement on a two-qubit system, the minimal volume ratio is $\mu_{2,1} = \frac{1}{2}$.

Here $\mu_{2,1}$ is the minimum over Hermitian two-qubit observables $A$ of
$\operatorname{vol}L_{\mathrm{Sep}}(A)/\operatorname{vol}L(A)$, where
$L_X(A)=\{\operatorname{Tr}\rho A\mid\rho\in X\}$ for the set of all states
($L$) or of separable states ($L_{\mathrm{Sep}}$), and vol is the Euclidean
volume (Definitions 1 and 2). The paper proves $\mu_{2,1}\ge\sqrt2-1$
(Proposition 7) and $\mu_{2,1}\le\frac12$ with the projector onto
$|\phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$.

## Motivation

An experiment detects entanglement with statistical confidence only when
its confidence region misses the separable numerical range, so a small ratio
$\operatorname{vol}L_{\mathrm{Sep}}/\operatorname{vol}L$ makes detection
easier. The conjecture fixes the best possible ratio for one two-qubit
observable. The frozen declaration
`D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.result` proves it.

## Gap

Issue #12146 classifies the conjecture as Tier 1 and records the literature
checks before any Lean:

- arXiv:2107.04365 has one version, and the published version states the
  conjecture;
- the seven citing works listed by Crossref (Sauer–Bernád 2022, Szymański's
  2022 thesis, Balanzó-Juandó–Studziński–Huber 2024, Wang–Bernád 2025,
  Pikul et al. arXiv:2510.27670, Li–Wang arXiv:2605.24360, Zhang–Xie
  arXiv:2601.01858) do not prove or refute it;
- an adversarial search of product numerical ranges, entanglement gaps,
  robustness and common noise, and base norms found no publication of the
  width inequality or of a noise operator shared by two states.

These are orchestrator-reported readings and seat-reported readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty. The rank-two step (Route, step 3) also follows from the rank-two
concurrence theorem of Hill–Wootters, PRL 78, 5022 (1997); the conjecture
needs in addition the shared noise of step 4.

## Route

Write two-qubit vectors in the magic basis: $u_{00}=(z_0+iz_1)/\sqrt2$,
$u_{11}=(z_0-iz_1)/\sqrt2$, $u_{01}=(iz_2+z_3)/\sqrt2$,
$u_{10}=(iz_2-z_3)/\sqrt2$. This is unitary, and
$u_{00}u_{11}-u_{01}u_{10}=z^Tz/2$.

1. $u$ is a product vector $a\otimes b$ exactly when $z^Tz=0$, and the
   projector of $a\otimes b$ is $(aa^*)\otimes(bb^*)$.
2. After a phase, $z^Tz=C$ with $0\le C\le\|z\|^2=1$.
3. For a real unit $r\perp\operatorname{Re}z$, put
   $\eta=(\operatorname{Im}z)\cdot r$, $\delta=\sqrt{\eta^2+C}$ and
   $t_\pm=-\eta\pm\delta$. The vectors $z+it_\pm r$ are product vectors, and
   with weights $(\delta\pm\eta)/(2\delta)$ their projectors sum to
   $zz^*+C\,rr^T$, which is therefore separable.
4. For unit $u,v$ take orthonormal real $r,s$ orthogonal to
   $\operatorname{Re}z_u$ and $\operatorname{Re}z_v$, and
   $N=(rr^T+ss^T)/2$, a separable state. With $c=\max(C_u,C_v)$ both
   $(P_u+cN)/(1+c)$ and $(P_v+cN)/(1+c)$ are separable states, and their
   difference is $(P_u-P_v)/(1+c)$.
5. So $\langle u,Au\rangle-\langle v,Av\rangle\le 2\,(\sup L_{\mathrm{Sep}}(A)-
   \inf L_{\mathrm{Sep}}(A))$; by the spectral decomposition of states the
   same bound holds for any two states.
6. $L_{\mathrm{Sep}}(A)$ is a bounded interval, so
   $\operatorname{vol}L(A)\le 2\operatorname{vol}L_{\mathrm{Sep}}(A)$.
7. For $A=|\phi^+\rangle\langle\phi^+|$, $L(A)\supseteq[0,1]$, and a product
   state $\sigma\otimes\tau$ has expectation
   $\frac12\sum_{a,b}\sigma_{ab}\tau_{ab}\in[0,\frac12]$; so the ratio is
   $\frac12$.

## Falsifier

The kernel-checked `result` states that $\frac12$ is the least element of
the set of ratios $\operatorname{vol}L_{\mathrm{Sep}}(A)/\operatorname{vol}L(A)$
over Hermitian $A$ with $\operatorname{vol}L(A)\ne0$, with vol the Lebesgue
measure on $\mathbb R$. A different definition of separability, of the
volume, or of the set over which the minimum is taken changes the question.

## Evidence

A NumPy recomputation of the construction (seed 20261002, 2000 random pairs
of unit vectors, half orthonormal) reconstructs $P_u+cN$ from the product
vectors of steps 3–4 with maximum entrywise residual $3.3\times10^{-16}$;
every product vector has normalized $|u_{00}u_{11}-u_{01}u_{10}|\le
5.3\times10^{-16}$, every weight is nonnegative, and $1+c\le1.9990$.
Dropping the hypothesis $r\perp\operatorname{Re}z$ makes all 2000 vectors
$z+it_\pm r$ non-product (issue #12146).

The canonical source is
`D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.lean`. Its public
declarations are `states`, `separableStates`, `numericalRange`, `claim` and
`result`. The frozen module state has statement identity
`sha256:ad9f39c042bc8c66c3f49d5e7591844b00204df42e745402b5e1df9e5ed191d7`. The
result declaration has statement identity
`sha256:8c35814a5581b8dd85f6068c299608bb3ab6358ca90eb7b729ad3bb8ebd2a1e0`. The
Freeze event is
`sha256:914b5b5f88db539920b49ca32941a150c277dcf0f10248d8d2ae017eac123a1c`; its
project-level frozen prerequisite is the Freeze event of
`D5/S3/Resource/EntanglementWitness` (through which the module imports
`CompositeCones` and `CompositeConeDuality`). The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 published conjecture; resolution `Proved` by
`D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.result`.
`proof_shape: content`; `admission_basis: open-problem-resolution` (issue
#12146). Utility kind `none` (a theorem about every two-qubit observable).

### What the settlement shows

- **Proved by `result`:** $\operatorname{vol}L_{\mathrm{Sep}}(A)\ge\frac12
  \operatorname{vol}L(A)$ for every Hermitian two-qubit $A$, with equality
  for the Bell projector; so $\mu_{2,1}=\frac12$.
- **Proved inside the proof of `result`:** for any two unit vectors $u,v$
  there is $c\in[0,1]$ and separable states $\sigma,\tau$ with
  $P_u-P_v=(1+c)(\sigma-\tau)$, where $c$ is the larger of the
  concurrences $|z_u^Tz_u|$ and $|z_v^Tz_v|$.
- **Follows from it (not stated in Lean):** for extreme eigenvectors $u,v$
  of $A$, $\operatorname{vol}L_{\mathrm{Sep}}(A)\ge(\lambda_{\max}-
  \lambda_{\min})/(1+\max(C_u,C_v))$, so the ratio exceeds $\frac12$
  whenever $A$ has extreme eigenvectors $u,v$ neither of which is maximally
  entangled ($C_u,C_v<1$).
- **Mechanism:** the noise operator is chosen once for both states, from
  two real directions orthogonal to the real parts of both magic coordinate
  vectors, which exist because these real parts span at most two of the four
  dimensions of $\mathbb R^4$.
- **Open here:** the values of $\mu_{2,k}$ for $k\ge2$ (the paper's
  Table 1), of $\mu_{d,1}$ for larger local dimension, and whether the
  common-noise construction extends beyond $2\times2$.

## ASSUMED-UNVERIFIED

The literature checks do not establish worldwide priority or absence of an
independent answer. The Lean kernel verifies the encoded statement and its
axiom closure; its correspondence to the paper, including the reading of
the minimum as the least element over observables with nonzero range and
of separability as the frozen `separableCone` with unit trace, is checked by
reading the source and the definitions.
