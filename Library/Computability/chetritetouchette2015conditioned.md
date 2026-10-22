---
bibkey: chetritetouchette2015conditioned
authors: Raphaël Chetrite; Hugo Touchette
year: 2015
title: Nonequilibrium Markov processes conditioned on large deviations
doi: 10.1007/s00023-014-0375-8
url: https://arxiv.org/abs/1405.5157
claim: A space-time harmonic Doob transform changes path measure by the ratio of terminal and initial harmonic weights; finite successful-path conditioning is a discrete instance.
strata_touched: []
license: citation-only
triage: anchor
---

# Successful-path conditioning and its computational contract

The primary preprint [§IV.2, equations (86)–(87)](https://arxiv.org/html/1405.5157v3#S4.SS2)
states the space-time harmonic condition and the endpoint ratio for the
changed path measure. Its large-deviation equivalence results concern a
different asymptotic problem. The finite discrete calculation below is
self-contained; it needs neither a large-deviation principle nor a limit.
The retry and relative-entropy calculations are elementary supporting
exposition, not additional theorems attributed to this paper.

## 1. Finite-horizon success conditioning

Fix a finite depth $L$, finite action sets, a fixed initial state $s_0$,
transition maps $T_t$, and proposal probabilities $q_t(a\mid s)$.
The state includes all information affecting the next proposal, legality,
update or final check. In particular a learned model's update state cannot
be omitted when it affects its subsequent proposals. Rejection and timeout
enter an absorbing failure state; stopped runs are padded to depth $L$.
Let $g(s_L)\in\{0,1\}$ be the verified terminal success indicator. Set

$$
h_L=g,\qquad
h_t(s)=\sum_a q_t(a\mid s)h_{t+1}(T_t(s,a)).
$$

Backward induction identifies $h_t(s)$ with the probability of eventual
success under the original proposal process. At $h_t(s)>0$, define

$$
q_t^*(a\mid s)=
\frac{q_t(a\mid s)h_{t+1}(T_t(s,a))}{h_t(s)}.
$$

The recursion normalizes this distribution. For a complete path $\gamma$
from $s_0$, multiplication telescopes:

$$
Q^*(\gamma)=Q(\gamma)\frac{g(s_L)}{h_0(s_0)}
=Q(\gamma\mid g=1),\qquad h_0(s_0)>0.
$$

Zero-$h$ states are unreachable from that initial state under the new law;
the policy there may be defined arbitrarily. A successful path outside the
support of $Q$ does not make $h_0$ positive. If $h_0=0$, this conditional
law is undefined. Success with probability one is a property of the defined
law, not a construction of an efficient sampler or a free postselection
instruction.

For a uniformly constructible layered graph with polynomially many states
and edges, explicit polynomial depth, computable transitions and terminal
tests, backward dynamic programming is efficient when all intermediate
number representations and arithmetic costs are polynomial. Abstract
state counts alone do not supply its representation or reconstruction of
real actions and a certificate. Exact rational sampling from fair bits
can have unbounded worst-case bit consumption; expected polynomial
sampling costs and bounded-error finite cutoffs are separate contracts.
To find one path it suffices to compute Boolean positive support and choose
a positive-probability action leading to positive support. This avoids
exact sampling and counting, while still charging graph construction,
support computation, execution and output.

## 2. Adaptive retries and recognizable progress

Let $\tau$ be the first successful attempt. Suppose, conditional on every
positive-probability history of failures, the next complete attempt has
success probability at least $\varepsilon\in(0,1]$. Iterated conditioning
gives

$$
\Pr(\tau>T)\le(1-\varepsilon)^T\le e^{-\varepsilon T},
\qquad \mathbb E\tau\le\varepsilon^{-1}.
$$

Indeed the next failure multiplies the preceding survival probability by
at most $1-\varepsilon$; sum this geometric tail. No independence of
attempts is required. If the full cost of every attempt, including model
updates, is at most $C(n)$, expected total cost is at most
$C(n)/\varepsilon$. For at most $M(n)$ progress stages, the corresponding
bound is $M(n)C(n)/\varepsilon(n)$ if each stage's progress is reliably
recognized and its conditional success bound holds after all preceding
history. Verifying that a new lemma is true does not by itself verify
that it supplies the claimed progress toward the task.

## 3. Successful mass and relative entropy

Let $Q$ be a distribution on a finite trajectory space, $G$ its success
set, and $p=Q(G)>0$. For every distribution $R$ supported on $G$,

$$
D_{\rm KL}(R\|Q)
=D_{\rm KL}(R\|Q(\cdot\mid G))-\ln p.
$$

This follows by substituting $Q(\gamma)=pQ(\gamma\mid G)$ in the finite
sum. Terms with positive $R$ and zero $Q$ make both relative entropies
infinite. Nonnegativity and $R=Q(\cdot\mid G)$ therefore give

$$
\inf_{R:R(G)=1}D_{\rm KL}(R\|Q)=-\ln Q(G).
$$

If $G$ is nonempty but $Q(G)=0$, every such divergence is infinite.
For an empty success set there is no admissible $R$. These conventions do
not create a conditional policy in either case. Under independent retries
with the same law, expected attempts are $1/p=\exp(-\ln p)$; the adaptive
bound in §2 instead uses the actual history-dependent lower guarantee.

For finite histories $H_t$ with a fixed initial state, factorizing both
path laws and expanding the logarithm gives the chain rule

$$
D_{\rm KL}(R\|Q)=\sum_{t=0}^{L-1}\mathbb E_R
D_{\rm KL}\bigl(r_t(\cdot\mid H_t)\|q_t(\cdot\mid H_t)\bigr).
$$

Consequently a successful reference law with
$D_{\rm KL}(R_x\|Q_x)\le c\ln(n+2)$ implies
$Q_x(G_x)\ge(n+2)^{-c}$. This is a whole-trajectory, per-instance bound;
an average training loss is not the same guarantee. Obtaining the
successful reference law can itself require solving the search problem.
For a unique successful length-$L$ sequence with conditional correct-step
probability $0<c_0<1$ throughout its prefixes, success is $c_0^L$ and its
negative log mass is $-L\ln c_0$.

Shannon entropy alone does not locate the successful set: the distributions
$(1-\epsilon,\epsilon)$ and $(\epsilon,1-\epsilon)$ have equal entropy,
but opposite success masses when only their first outcome succeeds.
Likewise $H(f(X)\mid X)=0$ for a deterministic function says nothing about
the time needed to evaluate it. None of these quantities is automatically
a physical entropy or a physical clock.

The explicit two-seam application is [Selection Calculus §18](../../docs/develop/theory/AURIC_FIB_ATOM_SELECTION_CALCULUS.md#十八从接缝计数到成功条件化的原生生成).
The quantum resource contract is separate: [amplitude amplification](brassardhoyermoscatapp2002amplification.md)
requires a coherent preparation, its inverse and a success phase operation.
It changes independent-retry dependence $1/p$ to order $1/\sqrt p$ under
those hypotheses; it does not supply the conditioned law or its classical
completion probabilities.
