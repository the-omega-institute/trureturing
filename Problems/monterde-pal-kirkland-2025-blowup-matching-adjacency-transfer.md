---
slug: monterde-pal-kirkland-2025-blowup-matching-adjacency-transfer
bibkey: monterdepalkirkland2025blowup
doi: 10.1016/j.laa.2025.10.001
url: https://arxiv.org/abs/2504.11585v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer.result
---

# Integral adjacency support gives transfer through uniform clone matchings

## Problem

H. Monterde, H. Pal and S. Kirkland, *Laplacian quantum walks on blow-up graphs* (2025), arXiv:2504.11585v1, DOI 10.1016/j.laa.2025.10.001, ask in Section 11, Future work (`main.tex`, line 814):

> Lastly, we ask: does Theorem \ref{pt1} hold for the adjacency case? That is, if $n\equiv 0$ (mod 4), will the addition of an appropriate matching in $\up{n}G$ induce adjacency LPST?

Their Laplacian Theorem `pt1`, Section 10, Edge perturbation (`main.tex`, lines 666–668), states:

> Let $n\equiv 0$ (mod 4) and $v$ be a vertex in $G$ with $\sigma_v(G)\subset\Zl.$ Then the addition of a matching in $T_v$ results in LPST in $\up{n}G$ at $\frac{\pi}{2}$ between the end vertices of every edge inserted.  Moreover, the resulting graph is periodic at all vertices in $T_v$ that are not incident to the newly added edges with period $\frac{\pi}{2}.$

These quotations retain the source macros: `\up{n}G` denotes the $n$-fold blow-up and `\Zl` denotes the integers. In the source, $\sigma_v(G)$ is Laplacian eigenvalue support. The quotations were checked against the downloaded v1 TeX member `main.tex`, md5 `b21c68f0d57c75bbf8eb7530da0c4d04`; the definitions are discussed in [the literature note](../Library/Eigenstructure/monterdepalkirkland2025blowup.md).

Issue [#22707](https://github.com/the-omega-institute/trureturing/issues/22707) fixes the reading settled here. Let $G$ be a finite simple graph with adjacency matrix $A_G$, let $v$ have integral **adjacency** eigenvalue support, and let $4\mid n$. Choose a fixed-point-free involution $\rho$ of the $n$ clone indices and insert its perfect matching in **every** clone set. With vertices indexed by $(v,j)$, the resulting matrix is
$H=A_G\otimes J_n+I_m\otimes P_\rho$.
For every clone index $j$, the settlement proves adjacency perfect state transfer at $\pi/2$ between $(v,j)$ and $(v,\rho j)$. This answers the appropriate-matching reading; it does not assert the literal variant with a matching inserted only in $T_v$.

## Motivation

The construction gives a specified matching and transfer time from a local spectral hypothesis at $v$. Integral adjacency support is required only at the vertex whose clones are to transfer; the graph need not have integral spectrum at every vertex. A perfect matching in each clone set is also a matching in the whole blow-up, since the clone sets are disjoint. Thus the construction supplies an explicit meaning of an appropriate matching without requiring connectivity or a non-isolated starting vertex.

## Gap

The bounded literature check recorded in #22707 reports no settlement in its searched scope. The orchestrator's searches covered the adjacency predecessor Bhattacharjya–Monterde–Pal (2024), arXiv:2308.13887, Monterde (2024), arXiv:2401.00362, and the source. The search seat additionally reported checking Monterde–Pal (2025), arXiv:2505.07982v5, Ojha–Pal (2025), arXiv:2509.20749v1, and searches on Zenodo, ResearchGate, SSRN and GitHub. Those additional readings are seat-reported rather than independently reproduced here.

The issue's repository check distinguishes issues #14649 and #11607, which cite the source for other statements, and the different double-blow-up conjecture in `Problems/bhattacharjya-monterde-pal-2024-double-blow-up-pgst.md`. It also records the question as Problem 10 of H. Monterde's *Quantum pure state transfer* (2025 thesis), printed page 163; that thesis reading is issue-reported.

`not-found-in-searched-scope`.

## Route

In the graph-specific steps, $m,n\in\mathbb N$, $g$ is a simple graph on $\mathrm{Fin}\,m$ with decidable adjacency, and $A_G$ is its complex adjacency matrix. Write $A_0=A_G\otimes J_n$ and $B=I_m\otimes P_\rho$.

1. **Integral phases and base periodicity.** For $4\mid n$ and every integer $z$, `integral_phase` gives $\exp(i\pi nz/2)=1$. For a vertex $v$ satisfying `IntegralSupport g v` and $4\mid n$, `base_periodic` gives $\exp(i\pi nA_G/2)e_v=e_v$. It uses a Hermitian eigenbasis: eigenvectors with zero $v$-coordinate contribute nothing to this column, and every other eigenvector has an integer eigenvalue by `IntegralSupport`. Neither lemma requires $n\ne0$ or a neighbour of $v$.
2. **Commutation.** For any permutation $\rho$ of $\mathrm{Fin}\,n$, `blowup_commute` proves $A_0B=BA_0$, using $J_nP_\rho=P_\rho J_n=J_n$. Involutivity and the absence of fixed points are not hypotheses of this lemma.
3. **Matching evolution.** For a complex square matrix $b$ on any finite index type with decidable equality and $b^2=I$, `exp_involution` proves $\exp(i\pi b/2)=ib$. For a fixed-point-free involution $\rho$ of $\mathrm{Fin}\,n$, `matching_exp` applies this to $B$. For that same $\rho$, any $v\in\mathrm{Fin}\,m$ and $j\in\mathrm{Fin}\,n$, `matching_column` gives $Be_{(v,j)}=e_{(v,\rho j)}$.
4. **Blow-up columns.** For any complex matrix $a$ on $\mathrm{Fin}\,m$, any complex scalar $c$, $n\ne0$, $v\in\mathrm{Fin}\,m$ and $k\in\mathrm{Fin}\,n$, `blowup_exp_column` gives, at each coordinate $(w,l)$,
   $\bigl(\exp(c(a\otimes J_n))e_{(v,k)}\bigr)_{(w,l)}=(e_{(v,k)})_{(w,l)}+n^{-1}\bigl((\exp(cna)e_v)_w-(e_v)_w\bigr)$.
   This lemma does not assume that $a$ is Hermitian. Its proof compares the convergent exponential series, using `blowup_pow_succ`, which for any such $a$, any $m,n\in\mathbb N$ and $r\in\mathbb N$ gives $(a\otimes J_n)^{r+1}=n^r(a^{r+1}\otimes J_n)$.
5. **Transfer.** For $v$ with `IntegralSupport g v`, $4\mid n$, a fixed-point-free involution $\rho$ and $j\in\mathrm{Fin}\,n$, `transfer_column` gives $\exp(i\pi H/2)e_{(v,j)}=i e_{(v,\rho j)}$. Here $j\in\mathrm{Fin}\,n$ supplies $n\ne0$ for `blowup_exp_column`; `base_periodic` makes its correction zero. Commutation factors the exponential, and `matching_exp` and `matching_column` give the remaining action. The reused `hamiltonianPropagator_neg`, valid for any complex matrix on a finite index type with decidable equality and any real time, identifies the canonical propagator at negative time with $\exp(itH)$. Applying the column identity with $\rho j$ and using $\rho(\rho j)=j$, `result` obtains the squared modulus one required by `HasPST`.

## Falsifier

The settlement would miss the registered question if its support condition, graph perturbation or transfer predicate differed from the intended adjacency problem. The module uses:

- `IntegralSupport g v`: for every real $\lambda$ and complex vector $x$, if $A_Gx=\lambda x$ and $x_v\ne0$, then $\lambda$ equals an integer;
- `blowUpMatching g n ρ`: $A_G\otimes J_n+I_m\otimes P_\rho$, with the vertex coordinate first, reversing the source's clone-first ordering (`main.tex`, lines 126–128); the permutation matrix acts by the inverse permutation, which equals $\rho$ for an involution;
- `FixedPointFreeInvolution`: a permutation satisfying $\rho(\rho j)=j$ and $\rho j\ne j$ for every clone index;
- the reused `HasPST H t a b`: the squared modulus of the $(a,b)$ entry of $\exp(itH)$ is one.

The support correspondence and the equivalence with the source's vector formulation of transfer are argued below. The hypotheses permit isolated vertices; if $n=0$ there is no clone index $j$, so the result makes no transfer assertion. A matching confined to one clone set, arbitrary partial matchings, periodicity of unmatched clones and transfer at other times are outside the statement.

## Evidence

The canonical source is `D5/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer.lean`.

- **Proof.** It proves the parameterized `result` theorem, whose conclusion is `HasPST (blowUpMatching g n ρ.val) (Real.pi / 2) (v, j) (v, ρ.val j)` under the hypotheses stated above.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer.lean.json`.

Declaration statements:

- `result`: `sha256:6db9a3c39527bd80f3ce42255a4e439b3c921f75062574eeb257f16b9d9ca481`.

## Triage

Tier 1 question of a 2025 paper, preregistered in issue #22707 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $m,n\in\mathbb N$, simple graph $g$ on $\mathrm{Fin}\,m$ with decidable adjacency, vertex $v\in\mathrm{Fin}\,m$, fixed-point-free involution $\rho$ on $\mathrm{Fin}\,n$, integral adjacency support at $v$, $4\mid n$ and clone index $j\in\mathrm{Fin}\,n$, the $((v,j),(v,\rho j))$ entry of $\exp(i\pi\,\mathrm{blowUpMatching}(g,n,\rho)/2)$ has squared modulus one.

**Computed, not formalized** (orchestrator, recorded in #22707): the construction and the local-insertion boundary were checked numerically before preregistration.

**Argued, not formalized.**

- *Correspondence with spectral support and vertex transfer.* For a Hermitian adjacency matrix and its orthogonal eigenprojection $E_\lambda$, $E_\lambda e_v\ne0$ implies $(E_\lambda e_v)_v=\|E_\lambda e_v\|^2>0$, giving an eigenvector with nonzero $v$-coordinate. Conversely, an eigenvector $x$ with $x_v\ne0$ satisfies $x=E_\lambda x$, so it cannot be orthogonal to $E_\lambda e_v$. Thus `IntegralSupport` expresses integral adjacency eigenvalue support. For a fixed-point-free involution, $P_\rho$ is symmetric with zero diagonal, and its edges lie inside clone sets where $A_G\otimes J_n$ has no edges; hence $H$ is the adjacency matrix of a simple undirected graph. Its exponential is unitary and symmetric. A unit-modulus entry forces all other entries of that column to vanish by its unit norm; symmetry aligns the row convention in `HasPST` with the source's vector convention.
- *Mechanism and an extension.* For a simple graph $g$ on $\mathrm{Fin}\,m$ with decidable adjacency, vertex $v$ with integral adjacency support and $4\mid n$, `base_periodic` gives base periodicity; with $n>0$, `blowup_exp_column` at $a=A_G$ and $c=i\pi/2$ makes the blow-up fix every clone of $v$. The matching supplies the swap. Even different perfect matchings in different clone sets preserve this argument: let $B$ have diagonal blocks $P_w$, each a fixed-point-free involutive permutation matrix on $\mathrm{Fin}\,n$. For every pair $u,w$, $(A_0B)_{uw}=(A_G)_{uw}J_nP_w=(A_G)_{uw}J_n$ and $(BA_0)_{uw}=(A_G)_{uw}P_uJ_n=(A_G)_{uw}J_n$. Also $B^2=I$. On the finite index set $\mathrm{Fin}\,m\times\mathrm{Fin}\,n$, `exp_involution` therefore gives $\exp(i\pi B/2)=iB$, and the column formula and base periodicity give transfer along the matching above $v$. This extension is not the statement of `result`.
- *Divisibility and sharpness.* The condition $4\mid n$ is sufficient for synchronizing all integral support phases, but is not necessary for every graph. For a nonempty edgeless base graph and any even $n\ge2$, $A_0=0$ and the graph is a union of matching edges; $B^2=I$ gives transfer at $\pi/2$ directly by `exp_involution`. In contrast, for $G=K_2$, $n=2$ and the matching in both clone sets, the graph is $K_4$. Its adjacency matrix $J_4-I_4$ has eigenvalues $3$ and $-1$, both with exponential $-i$ at time $\pi/2$, so the propagator is $-iI_4$ and has no transfer between distinct vertices at that time. Thus divisibility by four cannot simply be dropped from the uniform statement.
- *Why a local insertion needs a different argument.* Suppose $n>0$ and $v$ has a neighbour $w$. Insert a nonempty matching only in $T_v$, with adjacency block $M$. The $(w,v)$ block of $A_0B$ is $J_nM\ne0$, while the same block of $BA_0$ is zero. Consequently the commutation in `blowup_commute`, whose perturbation uses a permutation in every clone set, is unavailable for this local insertion. Noncommutation alone does not exclude PST. If $v$ is isolated, inserted matching edges above $v$ are isolated copies of $K_2$ and do give transfer at $\pi/2$; the neighbour hypothesis is essential to the obstruction just described. All-time nonexistence for the non-isolated local construction is not established here.
- *Effect on the source and neighbouring questions.* The settlement supplies an appropriate global matching for the last question of Section 11 under the registered integral-adjacency-support reading. No theorem in the checked v1 text assumes an affirmative answer to that question. The Laplacian Theorem `pt1` and Corollaries `pt2` and `pt3` remain separate source results; `result` supplies no adjacency analogue for their arbitrary local matchings or their periodicity assertions about unmatched clones. The preceding Section 11 question about weakly Hadamard diagonalizable graphs, necessity of integral adjacency support, other transfer times and the minimum number of inserted edges remain outside this settlement.

## ASSUMED-UNVERIFIED

The literature check is bounded by #22707 and does not establish exhaustive worldwide novelty or priority. Its external searches, related-paper readings and thesis Problem 10 were not independently reproduced. The arXiv v1 TeX was read directly; the journal text was not read, and the DOI, title and authors were checked through Crossref metadata.

The numerical checks attributed to the orchestrator were not rerun and establish no untested cases or all-time nonexistence. The search seat's irrationality argument for the local-insertion example, reported in #22707, was not reproduced and is not used as a settled conclusion. The statements under "Argued, not formalized", including the support and transfer correspondences, different-matchings extension, sharpness examples and local commutation obstruction, are not additional conclusions of `result`. Necessity of the spectral hypothesis, other times and minimal matching constructions remain open here.
