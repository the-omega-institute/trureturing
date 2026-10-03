---
slug: girard-2017-binegativity-upper-bound
bibkey: girard2017binegativity
doi: 10.48550/arXiv.1701.02724
url: https://arxiv.org/abs/1701.02724v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.result
---

# The upper binegativity bound for two qubits

## Problem

M. W. Girard, G. Gour, *The binegativity of two qubits*, arXiv:1701.02724v3
(2017), Eq. (9):

> In general, based on numerical evidence from randomly generated states,
> we conjecture that the the binegativity of two-qubit states is bounded by
> $\nu\frac{(c+\nu)(\nu+1)}{(c+\nu)^2+2c(1-c)}\leq N_2(\sigma)\leq
> \frac{\nu}{2}\frac{(c+\nu)^2}{c^2+\nu^2}$ for all states $\sigma$ with
> fixed negativity $N(\sigma)=\nu$ and concurrence $C(\sigma)=c$.

Here $N(\sigma)=2\operatorname{Tr}[(\sigma^\Gamma)_-]$ and
$N_2(\sigma)=\operatorname{Tr}[(\sigma^\Gamma)_-]+2\operatorname{Tr}[
(((\sigma^\Gamma)_-)^\Gamma)_-]$, with $X_\pm$ the positive and negative
components of a self-adjoint $X$ and $C$ the two-qubit concurrence. The
target is the upper inequality; it is a preprint conjecture (no journal
version is listed).

## Motivation

The binegativity is computable from the spectral decomposition of the
partial transpose, vanishes exactly on separable two-qubit states, and is
conjectured by the authors to be an entanglement monotone. Eq. (9) would
describe the region of possible values of $(C,N,N_2)$, and the paper uses
it to argue that the binegativity orders entangled states differently from
the concurrence and the negativity. The frozen declaration
`D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.result`
shows that the upper surface of that region is not an upper bound.

## Gap

Issue #12432 classifies the conjecture as Tier 1 and records the checks
made before any Lean:

- arXiv:1701.02724 v3 is the latest version and states the conjecture;
  INSPIRE lists one citation;
- Sazim–Awasthi, arXiv:1711.03717v2 (Phys. Lett. A 382 (2018) 1852), give
  $N_2=\frac N2\bigl(1+N(\rho_\psi)\bigr)$ with $\rho_\psi$ the normalized
  negative eigenvector of $\rho^\Gamma$ and study state families and noise
  channels, not the fixed-$(C,N)$ bound;
- concurrence–negativity relations (Verstraete et al., quant-ph/0108021;
  Miranowicz–Grudka, quant-ph/0404053) constrain $(C,N)$ only, and the
  operator positivity $|\rho^\Gamma|^\Gamma\ge0$ (Ishizaka,
  quant-ph/0308056) is a different statement.

These are seat-reported and orchestrator-reported readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty.

## Route

1. $\rho=\frac1{26}\bigl(vv^T+9|00\rangle\langle00|\bigr)$ with
   $v=(3,2,2,0)$ in the basis $00,01,10,11$.
2. With $w=(-1,1,1,2)$, $\rho^\Gamma=(\rho^\Gamma+ww^T/91)-ww^T/91$; the
   first part is $\frac{64}{91}l_1l_1^T+\frac5{52}l_2l_2^T+\frac4{65}l_3l_3^T$
   for rational $l_1,l_2,l_3$ and annihilates $w$, so the uniqueness of the
   positive and negative parts gives $(\rho^\Gamma)_-=ww^T/91$, of trace
   $1/13$.
3. With $z=(2,3,3,-2)$, the same argument gives
   $((ww^T/91)^\Gamma)_-=3zz^T/2366$, of trace $3/91$. Hence $N_2=1/7$.
4. $\operatorname{Tr}[A_-]=\sum_i\lambda_i(A)_-$ for Hermitian $A$, so
   $N=2/13$.
5. In any pure-state decomposition the zero entry $\rho_{11,11}$ forces
   $\psi_i(11)=0$ for every $\psi_i$ of positive weight, and the triangle
   inequality gives $\sum_ip_iC(\psi_i)\ge2|\rho_{01,10}|=4/13$; the
   decomposition with weights $9/13,1/26,7/26$ and vectors
   $(-7,-4,-4,0)/9$, $(1,-2,-2,0)/3$, $(1,0,0,0)$ shows the infimum is over a
   nonempty set. So $C\ge4/13$.
6. For $\nu=2/13$ and $c\ge4/13$,
   $9(c^2+\nu^2)-5(c+\nu)^2=2(2c-\nu)(c-2\nu)\ge0$, so the bound is at most
   $9/65<1/7$.

## Falsifier

The kernel-checked `result` is the negation of the statement that every
two-qubit density matrix $\sigma$ (`IsDensity`, positive semidefinite with
trace one) with positive negativity satisfies
$N_2(\sigma)\le\frac N2\frac{(C+N)^2}{C^2+N^2}$. The negativity is the frozen
`StructuredNegativityCoincidenceRefutation.negativity 2`, twice the sum of
the absolute values of the negative eigenvalues of the frozen
`partialTransposeB` (partial transposition on the second qubit); the
binegativity uses Mathlib's negative part; the concurrence is the infimum
over finite decompositions into unit vectors with nonnegative weights. The
refutation uses only a lower bound on the concurrence, since the bound
decreases in $c$ for $c>\nu$.

## Evidence

Exact recomputation (SymPy, issue #12432): $13\rho^\Gamma$ has eigenvalues
$2,-1,6\pm2\sqrt7$; Wootters' formula gives $C(\rho)=4/13$ (so the
convex-roof bound is attained); $N=2/13$, $N_2=1/7$; the upper bound is
$9/65$ (gap $2/455$) and the lower bound $5/39$ holds. A second independent
recomputation by the literature seat (characteristic polynomials, Gram
certificates, the spin-flip product) agrees.

The canonical source is
`D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.lean`.
Its public declarations are `TwoQubit`, `binegativity`, `pureConcurrence`,
`concurrence`, `claim`, `vec4`, `witness` and `result`; the partial
transposition, `IsDensity`, `negativity` and `eigenvalues` are frozen in
`D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation`.
The frozen module state has statement identity
`sha256:c166aa3f4c3cf9510f60ee56dd2a14f037202b3c299954aba9ef87dd1d69bd13`. The
result declaration has statement identity
`sha256:797223f7896ecb504da3573b596cab0819aedc8da21c22c10e588861af289ec0`. The
Freeze event is
`sha256:ed176054285b1816246cd4065eac0738d584fa0d98e3b274b78cf0014aa365ba`; its
project-level frozen prerequisite is the Freeze event of
`D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation`. The
proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 preprint conjecture; resolution `Refuted` by
`D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.result`.
`proof_shape: content`; `admission_basis: open-problem-resolution` (issue
#12432). Utility kind `certified-instance`, basis `refutes` the module's
`claim`.

### What the settlement shows

- **Proved by `result`:** the upper inequality of Eq. (9) fails for a
  rank-two two-qubit state, with $N_2=1/7$ against a bound of at most
  $9/65$.
- **Proved inside the proof of `result`:** the negative parts
  $(\rho^\Gamma)_-=ww^T/91$ and $((\rho^\Gamma)_-^\Gamma)_-=3zz^T/2366$; the
  identity $\operatorname{Tr}[A_-]=\sum_i\lambda_i(A)_-$ for Hermitian
  $A$; and the convex-roof bound $C\ge2|\rho_{01,10}|$ for states with
  $\rho_{11,11}=0$.
- **Mechanism (computed, not stated in Lean):** by the Sazim–Awasthi
  identity $N_2=\frac N2(1+N(\rho_\psi))$, the upper bound of Eq. (9) is
  equivalent to $N(\rho_\psi)\le2CN/(C^2+N^2)$ for the negative eigenvector
  $\psi$ of $\rho^\Gamma$. Here $\psi=w/\sqrt7$ has $N(\rho_\psi)=6/7$,
  while $2CN/(C^2+N^2)=4/5$: the negative eigenvector is more entangled than
  the surface allows. The paper's family $\sigma(p,q,r)$ of Appendix B, at
  the same $(c,\nu)$, ranges exactly over $[5/39,9/65]$ (endpoints
  $p=7/13$ and $p=3/13$), so the state lies outside the family that
  motivated the bound.
- **Checked by reading (orchestrator, issue #12432):** Appendix B, Eq.
  (appconc1) (l. 533–535), prints the lower bound with the prefactor
  $\nu/2$ instead of the $\nu$ of Eq. (9); the family's endpoint
  $5/39$ matches Eq. (9).
- **Follows from it (not stated in Lean):** by continuity of $N$, $N_2$ and
  $C$, full-rank states near $\rho$ (for instance $(1-\varepsilon)\rho+
  \varepsilon I/4$ for small $\varepsilon$) also violate the bound.
- **Open here:** the true largest binegativity at fixed $(C,N)$; whether the
  lower inequality of Eq. (9) holds for all states; and the conjecture that
  the binegativity is an entanglement monotone under LOCC or PPT channels.

## ASSUMED-UNVERIFIED

The literature checks do not establish worldwide priority, and a complete
forward-citation graph was not obtained; the Sazim–Awasthi and other
readings are seat-reported. The Lean kernel verifies the encoded statement
and its axiom closure; its correspondence to the paper, including the
convex-roof reading of the concurrence and the use of the second-qubit
partial transposition, is checked by reading the source and the
definitions.
