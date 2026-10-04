---
slug: iqbal-2025-pure-state-ecqc
bibkey: iqbal2025cqc
doi: 10.1007/s11128-026-05258-2
url: https://arxiv.org/abs/2509.08286v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/PureStateECQCRefutation.result
---

# Pure-state ECQC fails in dimension five

## Problem

H. Iqbal, *On the CQC Conjecture: A sufficient condition and an extension*,
arXiv:2509.08286v2, Closing Remarks and Future Works, p. 24, asks:

> So it would be interesting to develop a method to prove ECQC for pure states
> analytically, similar to the case of the original CQC conjecture.

The ECQC assertion is

$$
I(A:B)\geq\min_{S\subseteq\{0,\ldots,d\},\ |S|=d}
\sum_{i\in S}I(M_i^A:M_i^B).
$$

The source says: "The elements of the set $\mathcal{S}$ are collections of $d$
mutual information resulting from $d+1$ bipartite MUB measurements."
Issue #12896 preregisters its pure-state specialization at prime dimension five,
with Shannon and von Neumann entropy in bits and $0\log 0=0$.
The arXiv PDF labels the conjecture 3.1, §3.1, p. 6, and the dimension-five
bases §4.4.2, pp. 22–23; the preregistration identifies the same quoted content
as Conjecture 2.1 and §4.5.2.

## Motivation

`D5/S3/Quantum/Information/PureStateECQCRefutation.result` negates the universal
pure-state claim using the source's six bases. They are $M_0=F$, $M_1=I$,
and $M_{k+1}=D^kF$ for $k=1,\ldots,4$, where
$F_{xa}=\omega^{xa}/\sqrt5$, $D_{xx}=\omega^{x^2}$ and
$\omega=\exp(2\pi i/5)$.
Both parties use the same indexed column basis:
$p_i(a,b)=|\sum_{x,y}\overline{m_{i,a}(x)}\overline{m_{i,b}(y)}\psi(x,y)|^2$.
This convention reproduces the source's dimension-three isotropic calculation,
which has zero mutual information in the two quadratic bases.

## Gap

The checked arXiv v2 poses the pure-state question. Wang, Wang and Chen,
arXiv:2608.03828v3, refute general ECQC with a rank-two classical–classical
mixed state at dimension seven. Their pure-state sentence concerns CQC.
Qian, arXiv:2608.14806v2, treats two-basis CQC; its ECQC occurrence is a
bibliographic reference. Neither checked source supplies a pure-state ECQC
settlement. This literature check has the scope recorded in #12896 and does
not assert worldwide priority.

## Route

Take the normalized pure vector
$\psi=5^{-1/2}\sum_{x=0}^4|x\rangle|2x\bmod5\rangle$.
Since $1+2^2=0$ modulo five, the two quadratic phases cancel in every
noncomputational joint amplitude. Additive-character orthogonality leaves
$p_i(a,b)=\frac15[b=2a]$ for all six bases. Both marginals are uniform,
so each classical mutual information is $\log_2 5$.
Both partial-trace density matrices are $I/5$ and the global density is pure;
its quantum mutual information is $2\log_2 5$.
The minimum sum over five measurements is $5\log_2 5$, giving the strict
violation $3\log_2 5$.

## Falsifier

The refutation requires normalization, the same-basis measurement law, phase
cancellation in all six source generators, uniform marginals, the actual
partial traces and a strict comparison. These facts occur on the live path of
`result`. Replacing the second basis by its conjugate changes the assertion;
this module does not settle that replacement.

## Evidence

The canonical Lean module directly uses existing density-state, partial-trace,
classical-information and von Neumann entropy declarations. Its public surface
is `bases`, `jointLaw`, `claim` and `result : ¬ claim`.
The sole theorem is honestly classified `bind-only` and admitted as the
preregistered external `open-problem-resolution`; there are no private helper
theorems. The mathematical truth is the kernel-checked declaration and its
axiom closure, rather than the numerical computations below.

## Triage

Tier 1 published quant-ph question, preregistered in #12896; resolution:
**Refuted** at dimension five with the stated convention.
Utility: `certified-instance`, typed `refutes` edge to `claim`.
Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved in this module** (`PureStateECQCRefutation.result`): a maximally
  entangled pure state can repeat the full classical $\log_2 5$ correlation
  across all six source measurements. Purity and maximal local mixedness do
  not prevent the five-measurement sum from exceeding quantum information.
  The failure mechanism is cancellation of the quadratic phase under the
  pairing $x\mapsto2x$, rather than insufficient normalization or a different
  measurement convention.
- **Open for Lean formalization; analytic derivation**: for an odd prime $d$
  and $u^2=-1\pmod d$, the vector
  $\psi_u=d^{-1/2}\sum_x|x\rangle|ux\rangle$ has quadratic-basis amplitude
  $d^{-3/2}\sum_x\omega^{-k(1+u^2)x^2-(a+ub)x}
  =d^{-1/2}[a+ub=0]$. The computational law is $d^{-1}[b=ua]$;
  the linear condition gives the same bijection because $u^2=-1$.
  Uniform marginals give $d\log_2 d$ on the measurement side and
  $2\log_2 d$ on the quantum side, a violation $(d-2)\log_2 d$.
  Among odd primes a root exists exactly when $d\equiv1\pmod4$.
  At $d=2$ a root also exists but this family gives equality. The general
  dimension statement and its number-theoretic condition are separate
  formalization candidates, not results of this module.
- **Computed** (`python3 /Users/auric/.sshx/4d5197e63c823aead5c96fae/attempt-1/ecqc-numpy.py`):
  exhaustively among the 500 dimension-five states
  $5^{-1/2}\sum_x\omega^{cx^2+ex}|x\rangle|ux+v\rangle$
  ($u=1,2,3,4$; $v,c,e=0,\ldots,4$), exactly 50 are perfectly correlated in
  all six bases, all with $u\in\{2,3\}$. The Schmidt-rank-two state
  $(|00\rangle+|11\rangle)/\sqrt2$ violates by 0.1047442234152 bits under
  both same-basis and conjugate-basis conventions. The latter numerical
  observation is not a theorem of this module.
- **Computed** (same command, NumPy RNG seed 1, interleaved real/imaginary
  Gaussian draws, 20,000 normalized dimension-five vectors): zero sampled
  Haar violations; minimum quantum-minus-classical gap
  0.3320889666305926 bits. This finite sample did not detect the displayed structured witness; it is not a universal
  statement about Haar-random states. The finite structured family has Haar
  measure zero; no zero-measure claim is made for the full violating set.
- **Computed** (`python3 /Users/auric/.sshx/4d5197e63c823aead5c96fae/attempt-1/ecqc-perturb.py`):
  the normalized family $\sqrt{1-t^2}\psi+t|0,1\rangle$ still violates at
  $t=0.01,0.1,0.25,0.5$, respectively by
  6.9591076771894596, 6.564445676791794, 5.137460533580348 and
  1.9390574282495043 bits. **Open for formalization**: entropy continuity
  makes the strict comparison persist on a neighborhood and would imply
  positive Haar measure of the violating set; that neighborhood statement
  is not proved in this module.
- **Computed / open** (NumPy command above): in dimension three the 54 affine
  quadratic-phase states and 20,000 random maximally entangled states
  (seed 5) show no violation. Their minimum gaps are 1.584962500721156 and
  1.2642168569856405 bits. The dimension-three universal pure-state question
  remains open. In dimension seven, 28,000 sampled aligned Schmidt states
  (seed 2; 4,000 per rank) include a rank-four violation of
  1.7635455647231533 bits; its exact Lean settlement remains open.
- **Nearest surviving statements and source dependencies**: the numerical
  dimension-three observations remain finite-search results. The source's
  pure-state two-measurement CQC result is a different assertion and is not
  refuted here. Any proposed general pure-state ECQC proof or consequence
  using ECQC needs an added hypothesis, a restricted dimension range or a
  weaker bound. This module does not invalidate independently proved
  sufficient conditions or classify all such replacements. The earlier
  mixed-state dimension-seven refutation settles general ECQC; this result
  separately answers the source's pure-state question.

## ASSUMED-UNVERIFIED

The journal full text is unverified; the formal statement is tied to arXiv v2.
The finite numerical searches and general-dimension derivation are not
kernel-verified theorems. Dimension three, sharp replacement bounds,
classification of all violating states and the general-dimension/continuity
formalization candidates remain open. The numerical programs are host-side
experiments whose commands and parameters are given above; they do not enter
Lean's trust boundary.
