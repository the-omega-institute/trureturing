---
slug: meunson-deesuwan-2026-cumulant-renyi-qdpi
bibkey: meunson2026cumulant
doi: 10.48550/arXiv.2606.31205
url: https://arxiv.org/abs/2606.31205v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.result
---

# Data processing fails for the cumulant-based Rényi functional at every order above one

## Problem

A. Meunson and T. Deesuwan, *Cumulant-based quantum relative Rényi
functional*, arXiv:2606.31205v1, define for $\alpha>1$ (Definition 3,
Section IV)

$$S_\alpha^{Q}(\rho\Vert\sigma)=\frac{1}{\alpha-1}\ln\operatorname{Tr}
\left(\rho\,e^{(\alpha-1)(\ln\rho-\ln\sigma)}\right)$$

on pairs with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$.
The abstract and the conclusion state that the quantum data-processing
inequality (QDPI) for arbitrary CPTP maps remains open. The verbatim
sentences and Definition 3 are in
[the literature note](../Library/QuantumStates/meunson2026cumulant.md).
This question differs from Conjecture 15 of the same paper ($\alpha=0$,
commutativity-preserving channels), settled in
[the earlier dossier](meunson-deesuwan-2026-cop-relative-quantumness-refutation.md).

Issue [#13439](https://github.com/the-omega-institute/trureturing/issues/13439)
fixes the reading. `QDPI α` asserts
$S_\alpha(\mathcal N\rho\Vert\mathcal N\sigma)\le S_\alpha(\rho\Vert\sigma)$ for
every dimension $d$, every pair of positive definite density matrices and
every CPTP map $\mathcal N$ with positive definite outputs. Matrix logarithms
are continuous functional calculus, as in the frozen $\alpha=0$ module.
`claim` asserts that some $\alpha>1$ satisfies `QDPI α`. Faithful inputs meet
the support condition, so refuting this restricted claim refutes QDPI for the
paper's functional at every $\alpha>1$.

## Motivation

Data processing is the property that makes a Rényi-type quantity a
divergence: Petz Rényi divergences satisfy it for $\alpha\in(0,2]$ and
sandwiched ones for $\alpha\ge1/2$, as the paper recalls in Section III. The
paper offers the functional as a candidate quantum Rényi divergence; its
Section VII reports a preliminary study that found no violation for
$\alpha\in(0.9,1.3)$ in $10^4$ random qubit pairs per run.
`D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.result` shows
that the inequality fails at every $\alpha>1$.

## Gap

Issue #13439 records the literature check before any Lean. The paper has a
single version; the abstract and conclusion state the question as open. The
earlier study (J. Phys.: Conf. Ser. 3168 (2025) 012014) is numerical only.
The repository contains only the $\alpha=0$ refutation for this paper. The
search seat's bounded checks of INSPIRE, Google Scholar, MathDB and
formal-conjectures found no settlement; the Semantic Scholar citation API was
rate limited. `not-found-in-searched-scope`.

## Route

Fix $\alpha>1$, put $t=\alpha-1$, $x=16^{1+1/t}$, $r=(x-1)/(x+1)$ and
$a=\tfrac12\ln x$.

1. **Witness.** $N=\tfrac12\begin{pmatrix}1&\sqrt3\\\sqrt3&-1\end{pmatrix}$
   and $Z=\operatorname{diag}(1,-1)$ are self-adjoint involutions, and so is
   $B=N-Z$. The states $\rho=(I+rN)/2$ and $\sigma=(I+rZ)/2$ are positive
   definite with trace one and spectrum $\{x/(x+1),1/(x+1)\}$. The channel is
   complete dephasing, with Kraus operators $\operatorname{diag}(1,0)$ and
   $\operatorname{diag}(0,1)$.
2. **Input.** Two-point functional calculus gives $\ln\rho=cI+aN$ and
   $\ln\sigma=cI+aZ$ with $c=\tfrac12\ln x-\ln(x+1)$. Hence
   $\ln\rho-\ln\sigma=aB$ and $e^{taB}=\cosh(ta)I+\sinh(ta)B$, so
   $$F_{\rm in}=\cosh(ta)+\tfrac r2\sinh(ta)<e^{ta}=x^{t/2}=4^{t+1}.$$
3. **Output.** The outputs are $\operatorname{diag}(p_+,p_-)$ and
   $\operatorname{diag}(q_+,q_-)$ with $p_-=(x+3)/(4(x+1))>1/4$ and
   $q_-=1/(x+1)$, both positive definite. So
   $$F_{\rm out}=p_+^{t+1}q_+^{-t}+p_-^{t+1}q_-^{-t}
   >\tfrac14\left(\tfrac{x+3}{4}\right)^t>4^{-t-1}x^t=4^{t+1}>F_{\rm in}.$$
4. Strict monotonicity of $\ln$ and $1/t>0$ give
   $S_\alpha(\Phi\rho\Vert\Phi\sigma)>S_\alpha(\rho\Vert\sigma)$, contradicting
   `QDPI α`.

## Falsifier

The proof would fail if $B=N-Z$ were not an involution, if the dephasing map
were not CPTP, or if the scalar comparison
$t\ln x=2(t+1)\ln4$ did not place $F_{\rm in}$ below $4^{t+1}$.

## Evidence

The canonical source is
`D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.lean`. Its public
declarations are `cuRenyi`, `QDPI`, `claim` and `result`; the witness and
twenty supporting identities are private. Its direct frozen dependencies are
`IsDensity` and `IsCPTP` of
`D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation` and `MatrixMap`,
`MatrixMap.of_kraus` and `MatrixMap.of_kraus_isCompletelyPositive` of
`D5/S3/Quantum/Foundation/FiniteKrausChannel`. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom. The module builds in 18 s with a peak resident
set of 3.1 GB.

Numerical check (mpmath, 60 digits): at $x=16^{1+1/t}$ the increase
$S_{\rm out}-S_{\rm in}$ is 8.58, 1.57, 0.342 and 0.213 at $\alpha=1.05$,
1.25, 2 and 3. Positive control: a commuting pair under the same channel
gives equal values (0.328504066972 before and after).

## Triage

Tier 1 question stated in the abstract and conclusion of a 2026 paper,
preregistered in issue #13439 before any Lean. `theorem`; resolution
`refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

The twenty private theorems are bind-only and each is used on the proof path
of `result` (CLAUDE.md §3.2 「有消费的辅助声明」). Utility is
`certified-instance` with a typed `refutes` edge to `claim`; there is no
digestion atom.

### What the settlement shows

**Proved by `result`:** QDPI fails at every $\alpha>1$, already for qubits,
for positive definite inputs with positive definite outputs, and for a
unital channel. Restricting the dimension, requiring faithful states or
unital channels does not restore the inequality.

**Mechanism (proved for this family).** The input states have the same
spectrum and Bloch directions $60^\circ$ apart, so the large parts of
$\ln\rho$ and $\ln\sigma$ cancel: $\ln\rho-\ln\sigma=\tfrac12\ln x\,(N-Z)$
has operator norm $\tfrac12\ln x$, and $F_{\rm in}<x^{t/2}$. Dephasing keeps
weight above $1/4$ of $\Phi\rho$ on the basis vector where $\Phi\sigma$ has
weight $1/(x+1)$, so the classical output value grows like $x^t$. The
functional measures the logarithm difference, which noncommutativity
shrinks, while the channel output sees the eigenvalue ratio itself.

**Argued, not formalized.**

- Complete dephasing sends every pair to diagonal matrices, which commute,
  so it is commutativity preserving. The analogue of the paper's CoP-QDPI
  for $\alpha>1$ therefore fails on the same witness.
- For a commuting input pair whose outputs commute, both sides reduce to
  classical Rényi divergences of distributions related by one stochastic
  matrix. The classical inequality for $\alpha>1$ is the frozen
  `D5/S3/RenyiDivergence/DataProcessingAboveOne.renyi_divergence_channel_le_of_one_lt_of_ac`,
  so a violation with commuting outputs needs noncommuting inputs, as here.
  The reduction step is not formalized.

**Computed (mpmath, 60 digits, grid $x=10^{k/40}$).** Within this family the
first violating eigenvalue ratio is about $7.1\cdot10^9$ at $\alpha=1.05$,
$3.5\cdot10^6$ at $1.1$, $9.4\cdot10^3$ at $1.25$, $631$ at $1.5$, $119$ at
$2$ and $40$ at $3$. At $x=3$ and $\alpha=1.25$ there is no violation
($S_{\rm out}=0.048<S_{\rm in}=0.172$). This is consistent with the random
sampling of Section VII, whose typical qubit states have moderate eigenvalue
ratios. The same formula extended to $\alpha<1$ also increases under the
channel in this family: the first violating ratio is about $30$ at
$\alpha=0.5$, $7.1\cdot10^4$ at $0.9$ and $6.0\cdot10^7$ at $0.95$.

**Open.** Whether violations exist near $\alpha=1$ with bounded eigenvalue
ratio, a characterization of channels or state pairs on which the functional
contracts, and a proof for $\alpha<1$ are not established here.

**Effect on the paper.** The open question of the abstract and conclusion is
answered negatively for every $\alpha>1$, so the functional is not a quantum
Rényi divergence in the sense of data processing at any $\alpha>1$. The
proved positivity, classical reduction, additivity, unitary invariance,
continuity and monotonicity in $\alpha$ do not depend on QDPI and are not
affected. The $\alpha=0$ conjecture was refuted separately.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof. The search seat's database
readings are seat-reported.
