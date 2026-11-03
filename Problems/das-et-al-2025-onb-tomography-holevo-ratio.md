---
slug: das-et-al-2025-onb-tomography-holevo-ratio
bibkey: dasetal2025holevo
doi: 10.22331/q-2025-09-30-1867
url: https://arxiv.org/abs/2405.09622v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.result
---

# The NHCRB/HCRB ratio for full orthonormal qudit tomography is at most $d+1$

## Problem

A. Das, L. O. Conlon, J. Suzuki, S. K. Yung, P. K. Lam and S. M. Assad, *Holevo Cramér-Rao bound: How close can we get without entangling measurements?*, Quantum 9, 1867 (2025), DOI 10.22331/q-2025-09-30-1867; arXiv:2405.09622v2, Section 3.2.1, after Theorem 3, `DraftQuantumSubmission.tex`, lines 1147–1155:

> Although we prove an upper bound of~$d+2$, based on numerical evidence shown in Fig.~\ref{fig:estimateallarbitstate}, we expect the attainable bound to be~$d+1$ and expect~$\rat[\{\rho_\theta\}]$ to be maximised at~$\theta=0$ over~$\Theta$. Thus for the linear GMM model, we propose~$\rat[\{\rho_\theta\}]\leq d+1$.

The quotation preserves the TeX macros: `\rat` denotes $\mathcal R^{\mathrm{NH}}$. The source defines $\mathcal R^{\mathrm{NH}}[\{\rho_\theta\}]=\max_{\theta\in\Theta}\mathrm C_{\mathrm{NHCRB}}[\rho_\theta]/\mathrm C_{\mathrm{HCRB}}[\rho_\theta]$ in Eq. `ratiodef`, lines 798–801.

For $d\ge2$, put $n=d^2-1$. Let $b_1,\ldots,b_n$ be traceless Hermitian $d\times d$ complex matrices with $\operatorname{tr}(b_jb_k)=\delta_{jk}$, and let $\theta\in\mathbb R^n$. The model is $\rho_\theta=I_d/d+\sum_j\theta_jb_j$, with $\Theta$ consisting of the parameters making $\rho_\theta$ positive semidefinite. Its trace is one. This includes the source's generalized Gell-Mann model, whose normalization is specified in Section 5.2, lines 2071–2074.

The bounds use identity weight and the source's uncentered locally unbiased operators. Precisely:

- `IsLUB` requires every $X_k$ to be Hermitian, $\operatorname{tr}(\rho_\theta X_k)=\theta_k$, and $\operatorname{tr}(b_jX_k)=\delta_{jk}$.
- `zMatrix` has entries $Z_{jk}=\operatorname{tr}(\rho_\theta X_jX_k)$; `imPart` takes the entrywise imaginary part and embeds it back into complex matrices. The trace norm is $\lVert A\rVert_1=\operatorname{Re}\operatorname{tr}\sqrt{A^\dagger A}$.
- `IsAdmissible` requires Hermitian blocks $L_{jk}=L_{kj}$ and positive semidefiniteness of the matrix with blocks $L_{jk}-X_jX_k$, indexed by parameter–quantum pairs.
- `hcrb` is $\inf_X\{\operatorname{Re}\operatorname{tr}Z+\lVert\operatorname{Im}Z\rVert_1\}-\sum_j\theta_j^2$, over `IsLUB` families; `nhcrb` is $\inf_{X,L}\operatorname{Re}\sum_j\operatorname{tr}(\rho_\theta L_{jj})-\sum_j\theta_j^2$, over `IsLUB` families and `IsAdmissible` blocks.

These are the infimum forms of the source's Eqs. `HNCRBdefn`, `origunbiaseq` and `Holevodefn1`, lines 588–602 and 658–666. The definitions are also described in [the literature note](../Library/Estimation/dasetal2025holevo.md).

Issue [#25805](https://github.com/the-omega-institute/trureturing/issues/25805) fixes the settlement as the following multiplicative inequality: for every such $d,b,\theta$ with $\rho_\theta$ positive semidefinite, $\mathrm C_{\mathrm{NHCRB}}[\rho_\theta]\le(d+1)\mathrm C_{\mathrm{HCRB}}[\rho_\theta]$. This is `claim`, proved by `result`.

## Motivation

The two bounds compare precision limits in multiparameter quantum estimation. HCRB describes the collective-measurement bound, while NHCRB lower-bounds the attainable separable-measurement cost. Determining their largest ratio for full tomography separates the dimension dependence of this comparison from the general parameter-count bound. The distinction between NHCRB and an attainable separable cost matters: bounding NHCRB from above does not by itself bound the MICRB from above.

## Gap

Issue #25805 records the bounded literature check:

- The codex-cli search author read arXiv v1 and v2, the latest versions of twelve arXiv citing works listed by Semantic Scholar, the Quantum cited-by list, and two additional arXiv papers, and reported no settlement of the full-ONB $d+1$ bound.
- The orchestrator recorded no existing repository preregistration from searches for the source identifier and tomography.
- Moreva et al., APL Photonics 10, 010902 (2025), was inaccessible with HTTP 403.

The v2 conjecture is verified directly against the source quoted above. The other readings remain attributed to #25805: `not-found-in-searched-scope` does not establish exhaustive novelty or priority.

## Route

Throughout this route, $d\ge2$, $b$ satisfies `IsTracelessONB d b`, $\theta\in\mathbb R^{d^2-1}$, and $\rho=\operatorname{model}(d,b,\theta)$ is positive semidefinite. Write $P=\operatorname{Re}\operatorname{tr}(\rho^2)$, $S=\sum_j\theta_j^2$, and $B=(d^2-1)/d$.

1. **A unique locally unbiased family.** For any complex $d\times d$ matrix $A$, `matrix_expansion` gives $A=(\operatorname{tr}A/d)I+\sum_j\operatorname{tr}(b_jA)b_j$. Given a family $X$ satisfying `IsLUB d b θ X`, `unique_lub` proves $X=b$. Conversely, `basis_is_lub` proves that $b$ is locally unbiased for every real $\theta$. Thus `holevo_exact` identifies the Holevo cost set with a singleton and evaluates its infimum.
2. **The real contribution.** Under the same dimension and ONB hypotheses, `casimir` proves $\sum_jb_j^2=BI$, `purity_expansion` proves $P=1/d+S$, and `real_cost` proves $\operatorname{Re}\operatorname{tr}Z=B$ for $Z=\operatorname{zMatrix}(\rho,b)$. Hence the real contribution after subtraction is $B-S=d-P$.
3. **The imaginary contribution.** With all the route hypotheses, including positive semidefiniteness of $\rho$, `imaginary_bound` proves $dP-1\le\lVert\operatorname{Im}Z\rVert_1$. Its proof sets $A=i\operatorname{Im}Z$, verifies that $A$ is Hermitian, that $I+2A$ and $I-2A$ are positive semidefinite, and that $\operatorname{Re}\operatorname{tr}(A^2)=(dP-1)/2$. It applies `norm_contraction`, whose hypotheses are an arbitrary complex square matrix $A$ that is Hermitian and has both $I+2A$ and $I-2A$ positive semidefinite, and whose conclusion is $2\operatorname{Re}\operatorname{tr}(A^2)\le\lVert A\rVert_1$. Multiplication by $i$ preserves the trace norm. Under all the route hypotheses, `holevo_lower` combines these facts to prove $B\le\operatorname{hcrb}(d,b,\theta)$.
4. **A feasible NHCRB cost.** For $d\ge2$ and `IsTracelessONB d b`, `primal_admissible` proves admissibility of $L^*_{jk}=\frac{d+1}{d+2}(b_jb_k+b_kb_j+\delta_{jk}I)$. These are the blocks of Das et al., Eq. `optLmat`, lines 2393–2398, used in Eq. `upperboundNHCRB`, lines 2592–2617. Under the dimension and ONB hypotheses and for every real $\theta$, `primal_cost` evaluates their uncentered cost as $(d+1)B$. For any positive semidefinite $\rho$, any Hermitian family $X$, and any blocks $L$ satisfying `IsAdmissible X L`, `admissible_cost_nonneg` proves that the uncentered cost is nonnegative. Thus the NHCRB cost set is nonempty, by $X=b,L=L^*$, and bounded below by zero. Under all the route hypotheses, `nagaoka_upper` legitimately applies `csInf_le` to give $\operatorname{nhcrb}(d,b,\theta)\le(d+1)B-S$.
5. **Comparison.** Since $S\ge0$ and $d+1\ge0$, `result` combines `nagaoka_upper` and `holevo_lower` to obtain $\operatorname{nhcrb}(d,b,\theta)\le(d+1)B\le(d+1)\operatorname{hcrb}(d,b,\theta)$.

## Falsifier

A proof about a different normalization, centered operators without the matching subtraction, nonidentity weights, or an empty or unbounded infimum set would not settle this statement. Here the normalization and local unbiasedness equations agree with the source, both costs subtract the same $S$, and the block constraint acts on the full parameter–quantum index. `holevo_exact` supplies the singleton cost set; `nagaoka_upper` supplies both a feasible cost and a lower bound on every admissible cost. The use of `sInf` therefore does not depend on its default value for an empty or unbounded set.

The hypotheses include singular positive semidefinite model states; they impose neither strict positivity nor a full-rank condition. They exclude $d=1$, incomplete operator families and arbitrary weights.

## Evidence

The canonical source is `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.lean.json`.

Declaration statements:

- `result`: `sha256:761b7572969d47eaff5f68c5e4c0d979a1b2e705faa47103087efae99990d1b5`;
- `claim`: `sha256:a910c606d39db3076d3a3ab94ffa25e62333e4ba9c2447efd06e5c54e21b26fc`.

## Triage

Tier 1 conjecture of a 2025 Quantum paper, preregistered in issue #25805 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural dimension $d\ge2$, every family of $d^2-1$ traceless Hermitian complex $d\times d$ matrices with $\operatorname{tr}(b_jb_k)=\delta_{jk}$, and every real parameter vector $\theta$ whose model matrix $I_d/d+\sum_j\theta_jb_j$ is positive semidefinite, the identity-weight infimum costs satisfy $\operatorname{nhcrb}(d,b,\theta)\le(d+1)\operatorname{hcrb}(d,b,\theta)$.

**Computed, not formalized:** None.

**Argued, not formalized**.

- *Mechanism and a purity-dependent consequence.* Under all the route hypotheses, `holevo_exact`, `real_cost`, `purity_expansion` and `imaginary_bound` give $\operatorname{hcrb}\ge d-P+(dP-1)=(d-1)(1+P)$. The imaginary covariance compensates for the decrease in the real contribution as purity rises. This stronger inequality is a consequence of the stated helper lemmas; it is not the statement of `result` or a separately declared lemma in the module.
- *Ratios and strictness.* Under all the route hypotheses, `holevo_lower` gives $\operatorname{hcrb}\ge B>0$, so division converts `result` into the pointwise ratio bound. If additionally $\theta\ne0$, then $S>0$, and `nagaoka_upper` gives $\operatorname{nhcrb}\le(d+1)B-S<(d+1)B\le(d+1)\operatorname{hcrb}$. Thus the ratio is strictly below $d+1$ away from $\theta=0$. These division and strictness consequences are not separate compiled declarations.
- *Sharpness, conditional on a source theorem.* Das et al. (2025), arXiv:2405.09622v2, Section 3.2.1, lines 1111–1112, state: “For ONB tomography of the maximally-mixed qudit state~$\rho_\mathrm{m}$, the collective enhancement~$\CNH[\rho_\mathrm{m}]/\CH[\rho_\mathrm{m}] = d+1$.” Here `\CNH` and `\CH` denote the NHCRB and HCRB. Conditional on that source equality, the universal inequality and the strictness argument identify $d+1$ as the maximum, attained only at $\theta=0$. The source's NHCRB lower-bound certificate at the maximally mixed state is not formalized in this module; `result` alone supplies the universal upper bound.
- *Scope and neighbouring questions.* The argument applies to every ONB and includes rank-deficient density matrices because its only state hypothesis is positive semidefiniteness of the model matrix. For fewer than $d^2-1$ directions the ONB expansion and uniqueness argument do not apply as stated. Nonidentity weights also change the cost. The corresponding extensions remain open here.
- *Effect on the paper.* The $d+2$ upper bound in Theorem 3 can be replaced by $d+1$ for identity-weight full ONB tomography. Together with the source equality just quoted, this settles the proposed maximum for that model. The broader conjecture for all smooth full-rank models in Section 4, lines 1860–1878, and its proposed $\mathcal R^{\mathrm{NH}}_n\le\min(n,d+1)$ consequence retain their unresolved weighted and partial-model cases. The MICRB comparison in Section 3.2.2 is also unaffected: the source's inequality $\mathrm C_{\mathrm{NHCRB}}\le\mathrm C_{\mathrm{MI}}$ gives no transfer of this NHCRB upper bound to MICRB. No existence of SIC POVMs or measurement attaining these costs is established by `result`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The v1 reading, citation-list completeness, repository-search negatives and citing-paper readings are recorded in #25805 and were not independently reproduced here. Its arXiv search scope comprises 2403.07106v1, 2407.12466v2, 2504.18324v3, 2510.25466v1, 2511.16645v4, 2512.20091v2, 2601.02689v1, 2608.00550v1, 2609.36874v1, 2610.02625v1, 2610.03657v1, 2610.28070v1, 2606.07747 and 2208.07386v3, together with the Quantum cited-by list. Moreva et al., APL Photonics 10, 010902 (2025), remains unread; #25805 records HTTP 403. The issue's computational runs were not reproduced from their original programs or data.

The statements in “Argued, not formalized” are not additional formal settlements. Sharpness and the maximum statement use the source's maximally mixed equality as an external premise; that equality and its lower-bound certificate were not independently verified here. General weights, incomplete models, the conjecture for all smooth full-rank models, fixed-purity extremizers, MICRB bounds, and operational attainability remain outside the formal claim. The concrete generalized Gell-Mann family and its identification with the paper's parameterization are not instantiated in a separate Lean declaration.
