---
slug: gachechiladze-wyderka-guhne-2018-three-product-observables
bibkey: gachechiladzewyderkaguhne2018ultrafine
doi: 10.1088/1751-8121/aad3dc
url: https://arxiv.org/abs/1805.06404v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/UltrafineThreeProductObservables.result
---

# Three product observables with useless pairs and a useful triple

## Problem

M. Gachechiladze, N. Wyderka and O. Gühne, *The structure of ultrafine entanglement witnesses*, J. Phys. A: Math. Theor. 51, 365307 (2018), arXiv:1805.06404v2, Summary, TeX source `uew-iop-revision.tex`, lines 750–752:

> For instance, it would be interesting to identify three product observables, for which each pair is useless for entanglement detection, but the whole triple is useful.

The same source defines separable states as the convex hull of pure product states (lines 113–114) and describes a useless pair by the fact that every possible pair of expectation values can originate from a separable state (lines 504–507).

Issue [#25940](https://github.com/the-omega-institute/trureturing/issues/25940) fixes the existential reading: find three Hermitian product observables $M_i=A_i\otimes B_i$ such that, for each distinct pair $i,j$ and every density matrix $\rho$, one separable density matrix $\sigma$ reproduces both expectations, whereas some density matrix has no separable density matrix reproducing all three expectations. The pairwise matching state may depend on the pair and on $\rho$. The module fixes both local dimensions to three. This existence statement is proved.

## Motivation

The question asks whether entanglement information can require three product-observable expectations even when every pair of expectations admits a separable explanation. It concerns the joint expectation vector, rather than the separate detection power of the individual observables. A two-qutrit example answers the source's request without requiring a classification of useful observable families.

## Gap

The bounded literature check recorded in #25940 reports:

- the question is present in arXiv:1805.06404v2;
- the candidate-search seat inspected the three citing works reported by OpenAlex and OpenCitations: Wu–Tang (2020, arXiv:2007.02717), Simnacher–Czartowski–Szymański–Życzkowski (2021, arXiv:2107.04365), and Zhu et al. (2022, Photonics Research 10, 2047), without finding the requested triple;
- that seat also checked the five later related arXiv items listed in the issue, without a settlement;
- the recorded repository issue and `Problems/` searches found no prior record.

`not-found-in-searched-scope`. The source question is directly checked; the citation coverage and the reported readings of later works are not independently reproduced.

## Route

Use indices $0,1,2$, put $\delta=1/100$, and define

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1),\qquad
T=\begin{pmatrix}0&1&0\\1&0&1\\0&1&0\end{pmatrix}.
$$

The witnesses supplied by the module's private definitions `alice` and `bob` are

$$
\begin{aligned}
A_0&=\operatorname{diag}(1,1,\delta),& A_1&=X\oplus[\delta],& A_2&=Z\oplus[\delta],\\
B_0&=2I_3+T,& B_1&=\operatorname{diag}(1,2,3),& B_2&=\operatorname{diag}(1,4,9).
\end{aligned}
$$

Set $M_i=A_i\otimes B_i$ and $H=M_0+M_1+M_2$. These matrices specify the settlement's construction, rather than a formula attributed to the paper.

1. **Separable pairwise explanations.** For any natural dimension $d$, indexed families of complex $d\times d$ matrices $a,b$, finite selection $s$, and unitary $u$, `diagonal_family_useless` assumes that all selected $u^*a_i u$ are diagonal, or that all selected $u^*b_i u$ are diagonal; it concludes `IsUseless` for their product observables on $s$. In the first case `left_diagonal_useless`, with the first of these diagonalization hypotheses, dephases a density matrix in the columns of $u$. The resulting matrix has the form $\sum_k |u_k\rangle\langle u_k|\otimes c_k$. The lemma `separable_blocks` requires this unitary $u$, positive semidefinite $d\times d$ blocks $c_k$ for every $k$, and total trace one, and concludes that the sum is separable. Spectral decomposition of the blocks supplies the finite convex combination of normalized product projectors. The second diagonalization case interchanges the tensor factors. For the displayed matrices, the Hadamard basis on Alice's first two coordinates handles $\{0,1\}$, Alice's standard basis handles $\{0,2\}$, and Bob's standard basis handles $\{1,2\}$. The lemma `pairs_useless` concludes uselessness for every $i,j\in\mathrm{Fin}\,3$ with $i\ne j$; `factors_hermitian` verifies both local Hermitian conditions for each $i$.
2. **A negative ground energy.** For this fixed $H$, `ground_state` supplies a real $\mu<0$ and a vector $g\in\mathbb C^3\otimes\mathbb C^3$ with $g^*g=1$, $Hg=\mu g$, and $Q=H-\mu I\succeq0$. Its spectral argument uses the diagonal entry $H_{(1,2),(1,2)}=-7$ to obtain negativity. The lemma `outside_psd` establishes $B_0+B_1+B_2\succeq0$ for these fixed matrices.
3. **No product vector at a negative eigenvalue.** For every real $\mu<0$ and $a,b\in\mathbb C^3$ with $a^*a=b^*b=1$, `no_product_ground` excludes $H(a\otimes b)=\mu(a\otimes b)$. Under these hypotheses, the third Alice coordinate and `outside_psd` force $a_2=0$. Write $c=a_1^2-a_0^2$, $e=2a_0a_1$ and $w=(1,2,3)$. Elimination in the remaining eigenvector equations gives $(cw_i+ew_i^2)b_i=0$. If $b$ has two distinct nonzero coordinates, the corresponding determinants $w_iw_j^2-w_jw_i^2$, equal to $2,6,6$ for increasing pairs, force $c=e=0$ and hence $a_0=a_1=0$. If $b$ has only one nonzero coordinate, an adjacent nonzero entry of $T$ forces the same contradiction. Normalization excludes both possibilities.
4. **Exclusion of a common separable explanation.** The lemma `separable_ground_exclusion` assumes a real $\mu$, $H-\mu I\succeq0$, absence of a $\mu$-eigenvector $a\otimes b$ for every normalized $a,b\in\mathbb C^3$, and `IsSeparable` for $\sigma$; it concludes $\operatorname{Re}\operatorname{Tr}(\sigma H)>\mu$. The positive semidefinite zero-quadratic-form criterion gives the strict inequality on each normalized product projector, and the strict half-space is convex, so it contains their convex hull. Applying this to the certificates from `ground_state` and `no_product_ground`, `triple_useful` excludes a separable density matrix matching all three expectations of $|g\rangle\langle g|$: adding the three matching equalities would give energy $\mu$. Finally `result : claim` packages the displayed factors, their Hermitian conditions, all distinct pairs, and the useful triple.

## Falsifier

The settlement would miss the question if different separable states were permitted for the two expectations within a selected pair, if local factors were not Hermitian, or if usefulness meant only failure of a restricted numerical search. The module avoids these readings:

- `IsDensity` means positive semidefinite with trace one.
- `IsSeparable` is the real convex hull of projectors $|a\otimes b\rangle\langle a\otimes b|$ with $a^*a=b^*b=1$, hence finite convex combinations as in the source.
- `IsUseless` quantifies over every density matrix and requires a single separable density matrix matching all selected complex trace expectations simultaneously; these expectations are real for the Hermitian observables in `claim`.
- `claim` quantifies over two families of three Hermitian $3\times3$ complex matrices, requires uselessness for every distinct pair, and negates uselessness for the full triple.

The proof uses a normalized eigenvector and a positive semidefinite spectral lower bound, with no numerical optimization premise or unevaluated infimum.

## Evidence

The canonical source is `D5/S3/Quantum/Measurements/UltrafineThreeProductObservables.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurements/UltrafineThreeProductObservables.lean.json`.

Declaration statements:

- `result`: `sha256:864eed95dfc79df32a73f802da6dcb7e79de02a0054de2ee81be7f94d920c859`;
- `claim`: `sha256:095b9e6b9b317c2fd419321e0a685e969140469879dfa924d26428103ab7d6b3`.

## Triage

Tier 1 question of a 2018 paper, preregistered in issue #25940 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** there exist two families of three Hermitian $3\times3$ complex matrices whose product observables have the following properties: for every distinct pair and every density matrix on $\mathbb C^3\otimes\mathbb C^3$, some separable density matrix matches both expectations, while for some density matrix no separable density matrix matches all three expectations.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Mechanism.* Pairwise explanations need not be compatible: the pair quantifiers allow three different matching separable states for the same input state. A common explanation of all three expectations would also explain their sum. For the fixed $H$, a real $\mu$ with $H-\mu I\succeq0$ and no normalized product $\mu$-eigenvector gives the strict separable bound of `separable_ground_exclusion`; the normalized ground state supplied by `ground_state` reaches $\mu$. Thus the obstruction is the missing common separable explanation.
- *A margin without a numerical bound.* For this fixed $H$ and ground value $\mu$, the energy is continuous on the compact set of products of two unit spheres. Its attained minimum is strictly larger than $\mu$ by the preceding product-vector exclusion, so there is some $\Delta>0$ with every product energy, and therefore every finite convex average, at least $\mu+\Delta$. For any fixed density matrix $\tau$ and $0\le p\le1$, the energy of $(1-p)|g\rangle\langle g|+p\tau$ tends to $\mu$ as $p\to0$, giving an argument for detection at sufficiently small positive admixture. Neither $\Delta$ nor a noise threshold is supplied by `result`.
- *Scope and neighbouring questions.* The formal claim concerns two qutrits and the construction fixes $t=1$ and $\delta=1/100$. Parameter families, the smallest possible local dimensions, classification of useful triples, and optimal robustness bounds remain open in this settlement.
- *Effect on the paper.* The construction answers the existence request in the Summary. No theorem in the source is stated conditional on this future-work example. The suggested connections to joint measurability and state characterization (Summary, lines 752–754) are not established by `result` and remain open here.

## ASSUMED-UNVERIFIED

The bounded literature check in #25940 does not establish exhaustive worldwide novelty or priority. The citation counts and the candidate-search seat's readings of Wu–Tang, Simnacher–Czartowski–Szymański–Życzkowski, Zhu et al., and arXiv:2605.24360, 2510.27670, 2512.18374, 2409.17689 and 2608.06235 have not been independently reproduced. The statements labelled "Argued, not formalized" are outside the formal claim. No quantitative robustness, parameter-uniform conclusion, minimal-dimension result, classification, or link to joint measurability or state characterization is claimed as formalized.
