---
slug: chen-kato-brandao-2020-trace-norm-cmi-contraction
bibkey: chen2020mpdoparent
doi: null
url: https://arxiv.org/abs/2010.14682v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.result
---

# A completely contractive data-processing inequality for the trace-norm CMI

## Problem

C.-F. Chen, K. Kato and F. G. S. L. Brandão, *Matrix Product Density Operators: when do they have
a local parent Hamiltonian?*, arXiv:2010.14682v3, Section III.C (PDF p. 17), Conjecture III.2:

> For any channel $\mathcal E: C \rightarrow C'$ with local contraction ratio
> $\eta_{1,C}:=\sup_{\rho_C,\rho'_C}\frac{\lVert\mathcal E_C[\rho_{C}]-\mathcal E_C[\rho'_{C}]\rVert_1 }{\lVert\rho_{C}-\rho'_{C}\rVert_1} <1$
> There exists a global constant $\eta < 1$ such that for any tripartite system $ABC$ and any
> state $\rho_{ABC}$, it holds that $I_1(A:C'|B)_{\mathcal E(\rho)} \le \eta I_1(A:C|B)_\rho$.

Here $I_1(A:C|B)=\lVert\rho_{ABC}-\rho_A\otimes\rho_{BC}\rVert_1-\lVert\rho_{AB}-\rho_A\otimes\rho_B\rVert_1$
(Definition 2, PDF p. 14). The verbatim texts are in
[the literature note](../Library/QuantumChannels/chen2020mpdoparent.md).
Issue [#14728](https://github.com/the-omega-institute/trureturing/issues/14728) preregisters the
reading over finite-dimensional Kraus channels and density matrices, and the refutation.

## Motivation

The source studies whether matrix product density operators are Gibbs states of quasi-local
parent Hamiltonians through the decay of conditional mutual information. Conjecture III.1 (the
entropic version, under trivial correctable algebra) and Conjecture III.2 (this trace-norm version,
under a strict local trace-distance contraction) would each make one step of the generating channel
shrink conditional correlations by a uniform factor and so give exponential decay.

## Gap

The source proves contraction for channels with a forgetful component and for partially invariant
channels in a strongly noisy regime, and does not know whether dimension factors are needed between
$\eta_{1,C}$ and $\eta$. The repository refuted Conjecture III.1 in
[its dossier](chen-kato-brandao-2020-completely-contractive-cmi.md); that witness has local
contraction ratio $1$ and does not meet the hypothesis of Conjecture III.2. The literature check in
#14728 found no settlement; `not-found-in-searched-scope`.

## Route

Let $\mathcal M$ act on a qubit $C$ with the four Kraus operators $K_k=\tfrac1{\sqrt2}|k\rangle\langle v_k|$,
$(v_0,v_1,v_2,v_3)=(|0\rangle,|1\rangle,|+\rangle,|-\rangle)$: it measures $Z$ or $X$ with probability
$1/2$ each and records basis and outcome in $C'=\mathbb C^4$.

1. For density matrices with $\rho-\rho'=\begin{pmatrix}x&y\\\bar y&-x\end{pmatrix}$,
   $\lVert\rho-\rho'\rVert_1=2\sqrt{x^2+|y|^2}$ and $\lVert\mathcal M(\rho)-\mathcal M(\rho')\rVert_1=|x|+|\operatorname{Re}y|$,
   so $\eta_{1,C}\le1/\sqrt2$.
2. Take qubits $A,B$ and $\rho_{ABC}=\tfrac12(|0\rangle\langle0|_A\otimes\Phi_{BC}+|1\rangle\langle1|_A\otimes\Psi_{BC})$
   with $\Phi,\Psi$ the projectors on $(|00\rangle+|11\rangle)/\sqrt2$ and $(|01\rangle-|10\rangle)/\sqrt2$.
   Then $\rho_{AB}=I/4=\rho_A\otimes\rho_B$ before and after $\mathcal M$.
3. $I_1(A:C|B)_\rho=1$ and $I_1(A:C'|B)_{\mathcal M(\rho)}=1$: after the measurement, in every recorded
   basis and outcome the conditional states of $B$ for $\Phi$ and for $\Psi$ are orthogonal, and the
   centred output $X$ satisfies $X^\dagger=X$, $X^2=I/256$, so $16X$ is a unitary witnessing
   $\lVert X\rVert_1\ge1$.
4. Any $\eta$ in the conjecture would satisfy $1\le\eta\cdot1$.

## Falsifier

An error in the local contraction bound, in either trace norm, or a reading of $\eta_{1,C}$ or $I_1$
different from the source. Positive controls in #14728: a partially depolarizing channel lowers
$I_1$ of the same state to $0.5$ and $0$, and over 300 random states the ratio under $\mathcal M$ stays
at most $0.6406$.

## Evidence

`D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.lean` defines `localContraction`,
`I1` and `claim` on finite Kraus channels (`of_kraus`) and the repository trace norm
(`FiniteTraceDistance.traceNorm`), and proves `result : ¬ claim`. It reuses the partial traces of
`PartialTraceMutualInformation`, whose `density_posSemidef` this delivery makes public, and the
trace-norm lemmas `traceNorm_eq_max_re_tr_U` and `traceNorm_add_le`. The axiom closure of `result`
is exactly `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry` or `native_decide`.
MODULE_STATEMENT_PLACEHOLDER

## Triage

Tier 1: a named conjecture of a 2020 paper, retained in its 2023 revision, preregistered in #14728
before any Lean. `theorem`; resolution `refuted`. `result` is content (the local contraction bound
over all pairs of qubit states and the two exact trace norms); admission basis
`open-problem-resolution`; utility `kind=certified-instance; basis=refutes`. There is no digestion
atom.

### What the refutation shows

- **Proved by `result`:** a qubit channel can contract every trace distance by the factor $1/\sqrt2$ and
  still leave the trace-norm CMI of a state with entangled side information unchanged. A strict local
  contraction ratio does not control conditional correlations through a uniform global factor.
- **Mechanism (proved within the derivation):** the side information $B$ is maximally entangled with
  $C$, and both measured bases are real; for every real measurement vector $v$ the conditional $B$
  states of $\Phi$ and $\Psi$ are orthogonal ($v^{T}Jv=0$ for $J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$),
  so $A$ stays perfectly correlated with $BC'$ although the channel forgets part of $C$.
- **Computed, not formalized (#14728):** for $\mathcal M_p$ measuring $Z$ with probability $p$ the local
  ratio is $\sqrt{p^2+(1-p)^2}<1$ for every $0<p<1$ and $I_1$ is still preserved; for the full-rank
  states $(1-\varepsilon)\rho+\varepsilon I/8$ the trace-norm ratio after/before is exactly $1$ at
  $\varepsilon=10^{-1},\dots,10^{-4}$, so a restriction to faithful states does not rescue the
  conjecture. The same state and channel keep the entropic CMI at one bit while the channel has
  trivial correctable algebra; for the faithful perturbations the entropic CMI strictly decreases
  with ratios $0.911$, $0.984$, $0.9976$, $0.99968$ tending to $1$.
- **Open:** whether a contraction holds with $\eta$ depending on $d_C$ or on additional structure of the
  channel (the source's question about dimension factors), and the trace-norm analogue of
  Proposition III.4 for MPDO generated by such channels.

## ASSUMED-UNVERIFIED

The literature check in #14728 is bounded and does not establish worldwide novelty or priority; the
journal status of the source was not checked beyond its arXiv record.
