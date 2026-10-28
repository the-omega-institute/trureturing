---
slug: yu-duan-xu-2017-schur-channel-diamond-equality
bibkey: yuduanxu2017unitarydistance
doi: 10.1109/TIT.2016.2641447
url: https://arxiv.org/abs/1201.1172
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.result
---

# Schur-channel diamond-distance equality

## Problem

Nengkun Yu, Runyao Duan and Quanhua Xu, *Bounds on the distance between a
unital quantum channel and the convex hull of unitary channels*, IEEE
Transactions on Information Theory 63(2), 1299–1310, Section V, Theorem 3,
Equation (8), ask:

> It seems quite likely that in Eq. (8) the first inequality should be strict and the second one should be an equality. However, this is still an unsettled issue.

The equality in the second inequality is
$D(\Phi,\operatorname{Conv}(U_d))=D(\Phi,\Lambda_d)$ for every Schur channel
$\Phi$, where $\Lambda_d=S_d\cap\operatorname{Conv}(U_d)$.
The distance is the unhalved diamond distance. The
[literature note](../Library/QuantumChannels/yuduanxu2017unitarydistance.md)
contains the definitions and source quotations. Preregistration
[#16745](https://github.com/the-omega-institute/trureturing/issues/16745)
specifies the full quantified statement.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Every dimension and every channel | `claim` quantifies natural `d` and `QuantumChannel (Fin d) (Fin d)` | Includes dimension zero; complete positivity and trace preservation are carried by the channel type. |
| Schur action $\Phi(X)=C\circ X$ on every matrix | `IsSchurChannel` | Literal existence of a matrix giving Hadamard action; no replacement by a recovery certificate. |
| Convex hull of unitary channels | `MixedUnitary` | Finite families, nonnegative real weights of sum one, and unitary conjugation on every complex matrix. |
| $\Lambda_d=S_d\cap\operatorname{Conv}(U_d)$ | `SchurMixedUnitary` | Literal intersection; diagonal mixtures are obtained in the proof. |
| Infimum of diamond distances | `distToSet` | Real `sInf` of the image of the unhalved `diamondDistance`; no attained minimum is assumed. |
| Equality in the second inequality of (8) | `result : claim` | Proved with the Schur hypothesis as the only additional hypothesis. |

## Motivation

`D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.result` identifies the
two approximation costs for the whole Schur family. An arbitrary mixed-unitary
competitor can be replaced by a diagonal-unitary mixture without increasing
its distance from the target Schur channel. The assertion concerns distance
and does not supply an algorithm for computing an optimal mixture.

## Gap

The source proves
$\tfrac12 D(\Phi,\Lambda_d)\leq D(\Phi,\operatorname{Conv}(U_d))\leq D(\Phi,\Lambda_d)$
and leaves the second equality unsettled. The literature screen recorded in
#16745 does not establish exhaustive novelty. Its completeness is
`ASSUMED-UNVERIFIED`.

## Route

Let $V|i\rangle=|i,i\rangle$. Retain the second copy while the input channel
acts on the first. Recovery has Kraus operators
$K_0=\sum_i|i\rangle\langle i,i|$ and
$K_{k,i}=|i\rangle\langle k,i|$ for $k\ne i$.
Their adjoint products sum to the identity. These channels define
$\Theta(T)=R\circ(T\otimes\mathrm{id})\circ\operatorname{Ad}_V$.
On a matrix unit, its off-diagonal coefficient is
$\langle i|T(E_{ij})|j\rangle$; the diagonal coefficient is
$\operatorname{Tr}(T(E_{ii}))$. Consequently $\Theta$ fixes Schur channels.

If $a_i=U_{ii}$ for a unitary $U$, then $|a_i|\leq1$. Write each $a_i$ as the
midpoint of two unit phases. Independent choices of the phases produce
$2^d$ diagonal unitaries whose uniform conjugation mixture equals
$\Theta(\operatorname{Ad}_U)$. Convex combinations preserve this property.
The reference-system construction and rectangular trace contraction give
$D(\Theta(T),\Theta(S))\leq D(T,S)$.
Apply this to each mixed-unitary competitor and use
$\Lambda_d\subseteq\operatorname{Conv}(U_d)$ to compare the two infima.
The identity channel makes both competitor sets nonempty, including at
$d=0$, and the diamond distances are bounded below by zero.

The copying constructions and their two supporting identities are reused
from `CoherentCopyCorrelationTax`; the finite Kraus channel constructor is
`FiniteKrausChannel.finite_kraus_quantum_channel`. The live proof uses the
canonical `FiniteDiamondDistance` reference constructions and
`FiniteTraceDistance` trace-norm facts. The source statement is retained
literally; the proof's auxiliary channels are private.

## Falsifier

A Schur channel with unequal distances would contradict `result`. The
proof does not require pointwise equality of recovery-error norms. That
stronger assertion has the qubit counterexample in Triage.

## Evidence

The kernel-checked settling declaration is
`D5.S3.QuantumChannels.SchurChannelMixedUnitaryDistance.result`.
Its axiom closure is contained in
$\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.
The declaration has `proof_shape: content` with
`escape_witness: trace_contract_rectangular`; the module's admission basis is
`open-problem-resolution (#16745; Proved)`. The rectangular Jordan argument
proves trace contraction for arbitrary finite input and output types.
`disk_midpoint_phases` is content because it constructs two unit phases for
every point of the complex unit disk. Its consumer is
`Theta_preserves_mixed`; rectangular contraction is consumed by
`Theta_pointwise_contract` and `Theta_diamond_contract`, and both branches
are consumed by `result`.

The escape audit is unfinished for `result` and the owner declarations
`CoherentCopyCorrelationTax.copyIsometry`,
`CoherentCopyCorrelationTax.copyIsometry_star_mul`,
`CoherentCopyCorrelationTax.copyMatrix_entry`,
`FiniteDiamondDistance.blockEquiv`, `InputInformationBalance.arGrouping` and
`ConicalDesignConcurrenceComparability.traceNorm_isometry`. Their missing
typed dependent reconstruction, lawful readout, source selection and
sensitivity/dependence evidence is
tracked in [#16913](https://github.com/the-omega-institute/trureturing/issues/16913).
No completed four-slot registration is asserted.

### Numerical experiment

[Experiment directory at commit `589825249525e0d0dbfa6bd87de6e2a3b54d5924`](https://github.com/the-omega-institute/trureturing-experiments/tree/589825249525e0d0dbfa6bd87de6e2a3b54d5924/docs/reports/yu-duan-xu-2017-schur-channel-diamond-equality).
From that directory, `python3 check.py` exits 0 with `ALL_OK`.
The script SHA-256 is
`b6e739c4219f46b7bb94a7038c801006bba80c69464793ad09a5dee005143db1`.
The same pinned script was independently executed with exit 0.
For dimensions $d=1,2,3,4,5$, it checks $V^*V=I$, Kraus completeness,
the matrix-unit formula on the generated random linear maps, fixation of
the generated random Schur channels, and equality with the diagonal phase
mixture for the generated random unitaries. The maximum residual is
$1.6\times10^{-15}$. These finite numerical readings are not a uniform
proof or an exhaustive search over channels.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Basis copying with a retained copy and coherent recovery defines $\Theta$ | **Kernel-checked:** private `AdV`, `recovery_complete`, `recovery`, `leftChannel` and `Theta`, consumed by `result`; the published owner identity is `CoherentCopyCorrelationTax.copyIsometry_star_mul`. |
| $\Theta$ fixes every Schur channel | **Kernel-checked:** private `Theta_fixes_schur`, consumed by `result`. |
| $\Theta$ sends mixed-unitary channels to diagonal-unitary mixtures | **Kernel-checked:** private `disk_midpoint_phases`, `phase_unitary_average` and `Theta_preserves_mixed`, on `result`'s proof path. Each original unitary is replaced by $2^d$ diagonal unitaries; an original mixture with $n$ terms has $n2^d$ terms before consolidation. |
| $\Theta$ contracts diamond distance | **Kernel-checked:** private `trace_contract_rectangular`, `Theta_pointwise_contract` and `Theta_diamond_contract`, consumed by `result`; arbitrary finite reference systems are included. |
| Diagonal competitors suffice for Schur targets | **Kernel-checked:** private `Theta_preserves_mixed`, `Theta_fixes_schur`, `Theta_diamond_contract` and `assembly_from_replacement` establish the competitor replacement used by `result`. This includes an optimal competitor if one exists and does not assert attainment. |
| First inequality of (8) is strict exactly when the common distance is positive | **Proved in prose:** put $\delta=D(\Phi,\Lambda_d)=D(\Phi,\operatorname{Conv}(U_d))\geq0$. Then $\delta/2<\delta$ if and only if $\delta>0$. At $\delta=0$ both sides vanish. This scalar consequence is not a separate Lean theorem. |
| Equivalence of positive distance with $\Phi\notin\Lambda_d$ | **Open in this formalization:** compactness/closedness and an attainment argument are not formalized. The equality theorem alone does not supply that bridge. |
| Literal pointwise equality of recovery errors | **Proved in prose (counterexample):** for the qubit input $\rho=|0\rangle\langle0|$, identity and bit-flip on the first factor after copying give $|00\rangle\langle00|$ and $|10\rangle\langle10|$. Their difference has trace norm $2$. Recovery sends both to $|0\rangle\langle0|$, so its error has trace norm $0$. The contraction inequality survives and suffices. |
| Closed form of the common distance | **Open:** no expression in the entries or spectrum of $C$ is supplied. |
| Quantum Birkhoff question beyond Schur channels | **Open:** the fixation property is specific to Schur channels; no conclusion for arbitrary unital channels is asserted. |
| Numerical checks | **Computed:** the pinned experiment above covers the generated instances in dimensions $1$ through $5$, exits 0 with `ALL_OK`, maximum residual $1.6\times10^{-15}$. |
| Literature status | **Literature reading:** Haagerup–Musat, arXiv:1408.6476, and Harris–Levene–Paulsen–Plosker–Rahaman, arXiv:1807.06491, do not answer this equality in the screen recorded in #16745. arXiv:1812.01449 is by Lovitz; its attribution to Bhat et al. in that issue is incorrect. Completeness is `ASSUMED-UNVERIFIED`. |

The decisive mechanism removes the factor-two loss for the second
inequality of (8), uniformly over all natural dimensions. The theorem
changes the distance comparison in that equation to equality; it neither
invalidates the source's lower bound nor supplies the missing
compactness bridge for the strictness formulation by nonmembership.
Other source results retain their stated hypotheses. No extension beyond
the Schur-fixed family is claimed.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are not established. Source
and literature checks in #16745 are attributed to the orchestrator; the
finite experiment is supporting numerical evidence. The typed four-slot
escape registration remains unfinished under #16913. Closed-form distance,
compactness/nonmembership and non-Schur extensions remain outside the
kernel-checked conclusion.
