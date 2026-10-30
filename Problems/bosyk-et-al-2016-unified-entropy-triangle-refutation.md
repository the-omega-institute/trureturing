---
slug: bosyk-et-al-2016-unified-entropy-triangle-refutation
bibkey: bosyketal2016unifiedcorrelations
doi: 10.1016/j.physa.2016.06.131
url: https://arxiv.org/abs/1604.00329v1
triage: theorem
motivation_gids:
  - D5/S3/Entropy/UnifiedEntropyTriangleRefutation.result
---

# The unified-entropy correlation triangle inequality is not universally valid

## Problem

G. M. Bosyk, G. Bellomo, S. Zozor, M. Portesi and P. W. Lamberti, *Unified entropic measures of quantum correlations induced by local measurements*, Physica A 462 (2016) 930–939, DOI 10.1016/j.physa.2016.06.131, arXiv:1604.00329v1, Concluding remarks, `Unifiedarxiv.tex`, lines 944–951:

> In the general case, we only proof this for the von Neumann and Tsallis with entropic index of order $2$, which follows from the contractivity property under a projective measurement of quantum relative entropy and Hilbert Schmidt distance, respectively. We provide numerical counterexamples where the local contractivity property of unilocal disturbances fails in a wide range of the entropic index of R\'enyi and Tsallis entropies, but it remains open if the triangle-like inequality is fulfilled for other entropic measures.

For $q>0$, $q\ne1$ and $s\ne0$, the source defines
$S_{(q,s)}(\rho)=((\operatorname{Tr}\rho^q)^s-1)/((1-q)s)$ and
$D^{\Pi^K}_{(q,s)}(\rho)=[S_{(q,s)}(\Pi^K(\rho))-S_{(q,s)}(\rho)]/(\operatorname{Tr}\rho^q)^s$.
The correlations $D^K_{(q,s)}$ are the minima over complete local rank-one projective measurements without postselection, for $K\in\{A,B,AB\}$. These definitions occur at lines 187–194, 371–394 and 418–433; the triangle-like inequality (38) is at lines 697–701. See also [the literature note](../Library/Entropy/bosyketal2016unifiedcorrelations.md).

Issue [#24210](https://github.com/the-omega-institute/trureturing/issues/24210) fixes the universal reading: for every admissible pair $(q,s)$ and every density matrix on a product of finite-dimensional complex spaces,
$D^{AB}_{(q,s)}(\rho)\le D^A_{(q,s)}(\rho)+D^B_{(q,s)}(\rho)$.
This reading is refuted at $(q,s)=(2,-1)$ by the two-qubit state

$\rho_0=\frac1{16}\begin{pmatrix}6&1&1&0\\1&2&0&1\\1&0&2&1\\0&1&1&6\end{pmatrix}$,

in coordinate order $00,01,10,11$.

## Motivation

The paper distinguishes the total correlation $D^{AB}$ from the two semiquantum correlations $D^A$ and $D^B$. A universal triangle-like inequality would control the disturbance from measuring both factors by the sum of the separately minimized disturbances, throughout the unified-entropy family. Its validity tests whether that relation survives the nonlinear entropy and the generalized-purity normalization.

## Gap

The bounded literature check recorded in #24210 reports:

- the source's v1 contains the open question, and the arXiv listing has no other version;
- searches for the triangle-like inequality with unified entropies and local projective measurements returned the paper and repository copies, with no settlement found;
- citation searches and the accessible citing material listed in the issue yielded no settlement; three subscription-only works were checked only in abstract;
- the repository searches recorded in the issue found no earlier preregistration or unified-entropy module.

The source question is checked directly against the v1 TeX. The other search readings are reported evidence, with the limits listed below. `not-found-in-searched-scope`.

## Route

All lemma names below are in `D5/S3/Entropy/UnifiedEntropyTriangleRefutation`; the witness and supporting lemmas are private.

1. **A density matrix.** For the fixed matrix $\rho_0$, `witness_posSemidef` proves positive semidefiniteness by a sum of nonnegative squared complex norms. `witness_trace` gives $\operatorname{Tr}\rho_0=1$, and `witness_purity` gives $P=\operatorname{Re}\operatorname{Tr}(\rho_0^2)=11/32$.
2. **The entropy reduction.** For Hermitian complex square matrices $\sigma,\rho$ on the same finite coordinate type with decidable equality, and with $\operatorname{Re}\operatorname{Tr}(\rho^2)\ne0$, `disturbance_two_neg_one` gives $D^{\Pi}_{(2,-1)}(\rho)=\operatorname{Re}\operatorname{Tr}(\rho^2)/\operatorname{Re}\operatorname{Tr}(\sigma^2)-1$ when $\sigma$ is the measured matrix. The underlying identity `genPurity_two` requires a Hermitian matrix and identifies its spectral-square trace with its matrix-square trace.
3. **Every qubit basis.** For each unitary $u\in U(2)$, `qubit_projectors` represents its first column projector by $(I+n\cdot\sigma)/2$ for a real unit vector $n$, and its second by the complementary projector; here $\sigma$ denotes the Pauli matrices. For arbitrary $u,v\in U(2)$ applied to the fixed witness, `measured_hermitian` gives Hermiticity of all three measured states, and `measured_purities` supplies real vectors $n,m$ with $\|n\|=\|m\|=1$ and purities
   $P_A(n)=(1+1/16+n_x^2/16+n_z^2/4)/4$,
   $P_B(m)=(1+1/16+m_x^2/16+m_z^2/4)/4$, and
   $P_{AB}(n,m)=(1+(n_x^2+m_x^2)/16+n_z^2m_z^2/4)/4$.
4. **Positive, attained bounds.** For real $n,m\in\mathbb R^3$ with $\|n\|=\|m\|=1$, `bloch_purity_bounds` bounds the displayed unilocal purities between $1/4$ and $21/64$ and the bilocal purity between $1/4$ and $5/16$. Consequently, `measured_purity_bounds` gives these bounds for every $u,v\in U(2)$ on $\rho_0$. `computational_purities` attains the upper bounds at $u=v=I$.
5. **Actual infima and contradiction.** For this fixed witness at $(2,-1)$, `correlations` bounds every unilocal disturbance below by $1/21$ and every bilocal disturbance below by $1/10$. The identity bases attain those bounds. Thus each range is nonempty and bounded below, and the attained bound is its least element; `IsLeast.csInf_eq` identifies its real infimum. This gives $D^A=D^B=1/21$ and $D^{AB}=1/10$. `result` applies `claim` at $q=2$, $s=-1$, both coordinate types $\mathrm{Fin}\,2$ and $\rho_0$, using the verified parameter conditions, positivity and trace. The resulting inequality is false, with difference $1/10-2/21=1/210>0$.

## Falsifier

A check of selected bases would not settle the inequality between the minimized measures. The module instead quantifies over every local unitary basis and proves a least element of each witness disturbance range.

The source-to-formal identification uses the columns of a unitary as a complete orthonormal basis, whose outer products are the complete rank-one projectors. `measureA`, `measureB` and `measureAB` sum the corresponding projector–state–projector products, without retaining an outcome. `genPurity` is the real trace of the real spectral power, and `disturbance` divides by the original state's spectral-power trace raised to $s$, as in equation (16).

`claim` ranges over real $q>0$, $q\ne1$, $s\ne0$, finite coordinate types with decidable equality, and positive semidefinite complex matrices of complex trace one. The correlation definitions use real infima rather than the source's minima; their attainment and lower boundedness are established for the witness, without asserting general attainment. Neither limiting index $q=1$ nor $s=0$ is included in `claim`.

## Evidence

The canonical source is `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.lean`.

- **Proof.** It defines `claim : Prop` and proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Entropy/UnifiedEntropyTriangleRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:a423d8df0dec99d380fba37f38e408576b3dfd8726ea11a51cdc3f8a2daa71a2`;
- `claim`: `sha256:3c0ca40ebf4d088c82c42192ce2d5d62d1f8b611d7f3d5c9df47cd7d18be983f`.

## Triage

Tier 1 question left open in the conclusions of a 2016 paper, preregistered in issue #24210 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal assertion that $D^{AB}_{(q,s)}(\rho)\le D^A_{(q,s)}(\rho)+D^B_{(q,s)}(\rho)$ for every real $q>0$ with $q\ne1$, every real $s\ne0$, every pair of finite coordinate types with decidable equality, and every positive semidefinite complex matrix $\rho$ of trace one on their product, is false; the three correlations are the unitary-basis infima defined above.

**Computed, not formalized:** none.

**Argued, not formalized.**

- *Mechanism and the missing condition.* For $\rho_0$, the optimal raw purity losses are $1/64$ on either factor and $1/32$ jointly: the raw losses add exactly. The reciprocal-purity disturbance at $(2,-1)$ turns those losses into a strictly larger joint cost. In the computational bases, the second disturbance on the already measured state is $(21/64)/(5/16)-1=1/20$, and its purity correction factor is $(11/32)/(21/64)=22/21$. Their product is $11/210>1/21$, the unilocal disturbance on the original state. Thus the weighted local contractivity required in the source's sufficient condition (lines 717–723) is violated here. Even a common pair of optimal bases does not supply that missing condition.
- *A range of indices for this same state.* For the fixed witness, `measured_purity_bounds` applies to all $u,v\in U(2)$ and `computational_purities` attains the upper bounds at $u=v=I$. For $q=2$ and any real $s\ne0$, the disturbance as a function of the positive purity ratio $r=P_{\Pi}/P$ is $(1-r^s)/s$, with derivative $-r^{s-1}<0$, so those bases still minimize it. The optimal ratios are $r_A=r_B=21/22$ and $r_{AB}=10/11$. Put $h_s(x)=(1-(1-x)^s)/s$ on $0\le x<1$. Then $h_s(0)=0$ and $h_s''(x)=(1-s)(1-x)^{s-2}$. Strict convexity gives $h_s(2/22)>2h_s(1/22)$ for every $s<1$, $s\ne0$; at $s=1$ there is equality, and strict concavity gives the reverse inequality for $s>1$. This extends the counterexample by an analytic argument, not by a declaration in the module.
- *Nearby statements and effect on the source.* The same state attains the triangle equality at the Tsallis index $(2,1)$, so this refutation does not contradict that restricted case. The source's conditional derivation from weighted local contractivity (lines 713–753) remains a conditional implication; the witness violates its hypothesis. Its restricted arguments for CQ, QC and CC states (lines 676–703), pseudopure states (lines 785–821), and Werner and isotropic states (lines 846–914) are not refuted by the failure of unrestricted validity. In the sections referring to (38), no further conclusion assuming its unrestricted validity is identified. Any use of (38) for all states and all admissible indices requires additional restrictions; a classification of the surviving indices and state classes remains open here.

## ASSUMED-UNVERIFIED

The bounded literature check in #24210 does not establish exhaustive worldwide novelty or priority. Its arXiv version inventory, web and repository search results, OpenAlex citation count of 13 and Semantic Scholar listing of 12 records are not independently reproduced here. The reported reading of Bellomo's 2017 thesis (DOI 10.35537/10915/59648), arXiv:1605.00806, 1711.00641, 1905.13717 and 1506.02090, and Axioms 9 (2020) 20 is not reproduced. The citing works with DOIs 10.1007/s11128-019-2416-1, 10.1007/s10773-024-05865-8 and 10.1007/s10915-024-02471-y were read only in abstract according to that record; their full texts are not checked here.

All statements labelled "Argued, not formalized" are outside the formal conclusion of `result`, including the extension to other $s$, the weighted-contractivity calculation and the assessment of other source statements. The general correspondence between complete rank-one projective measurements and unitary bases is the source-to-formal interpretation; no separate equivalence theorem is asserted. General attainment of the infima, the Rényi and von Neumann limiting measures, a classification of valid indices, and extensions to other states or dimensions are not established by this settlement.
