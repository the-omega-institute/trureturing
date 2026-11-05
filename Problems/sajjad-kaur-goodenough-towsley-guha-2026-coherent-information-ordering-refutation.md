---
slug: sajjad-kaur-goodenough-towsley-guha-2026-coherent-information-ordering-refutation
bibkey: sajjadkaurgoodenoughtowsleyguha2026noisygraph
doi: 10.22331/q-2026-05-21-2111
url: https://arxiv.org/abs/2404.09014v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.result
---

# Subsystem size does not order coherent information in noisy graph states

## Problem

A. Sajjad, E. Kaur, K. Goodenough, D. Towsley and S. Guha, *Lower bounds on bipartite entanglement in noisy graph states*, arXiv:2404.09014v2; Quantum 10, 2111 (2026), §5.4, “The subsystem with more qubits has higher coherent information?” (`main.tex`, line 951):

> In all of the examples that we have considered, we have observed that the subsystem  with the most qubits has the largest coherent information regardless of the types of the two subsystems and their distributions. Therefore, we conjecture that this is generally true but are unable to make a definitive statement.

The quotation is from the downloaded v2 TeX, `main.tex`, md5 `230ee16b992b9567441d518d7471253e`; the trailing TeX comment is omitted. The source's noise model is in §2.2, lines 186–194, and its entropy and coherent-information definitions are in §2.3, lines 201–216. See also [the literature note](../Library/QuantumContext/sajjadkaurgoodenoughtowsleyguha2026noisygraph.md).

Issue [#21154](https://github.com/the-omega-institute/trureturing/issues/21154) fixes the following non-strict reading. For natural numbers $n_A,n_B$ with $n_B<n_A$, let $G$ be any simple graph on $A\sqcup B$, where $|A|=n_A$ and $|B|=n_B$. Each qubit independently starts in

$\sigma_P=P\lvert+\rangle\langle+\rvert+(1-P)\lvert-\rangle\langle-\rvert$,

with the same $P\in[0,1]$. Put $\rho_G(P)=U_G\sigma_P^{\otimes(n_A+n_B)}U_G^\dagger$, where $U_G$ is the product of controlled-Z gates over the edges. Writing $\rho_A=\operatorname{Tr}_B\rho_G(P)$ and $\rho_B=\operatorname{Tr}_A\rho_G(P)$, define

$\mathcal I_A=H(\rho_A)-H(\rho_G(P))$, $\mathcal I_B=H(\rho_B)-H(\rho_G(P))$,

where $H$ is base-two von Neumann entropy. The module's `claim` asserts $\mathcal I_B\le\mathcal I_A$ for every such pair of sizes, every such graph with decidable adjacency, and every such $P$. Edges within either part are allowed. This non-strict assertion is refuted.

## Motivation

The source uses coherent information as a lower bound on distillable entanglement. Its §2.3, line 216, identifies $\max\{\mathcal I_A,\mathcal I_B\}$ as the tighter of the two bounds. The conjecture would allow the number of qubits alone to select that maximum without calculating both marginal entropies. The counterexample shows why the marginal structure matters even under identical independent noise on all qubits.

## Gap

The literature check recorded in #21154 before any Lean is bounded:

- the v2 source retains the conjecture, as the quotation above confirms;
- the reported OpenAlex record W4394867638 listed one citing work, Goodenough et al. (2024 preprint), *Bipartite entanglement of noisy stabilizer states through the lens of stabilizer codes*, arXiv:2406.02427v2, reported there as giving syndrome-entropy formulas without settling the subsystem-size ordering;
- the reported arXiv title and author searches found no later settlement; MathDB and `google-deepmind/formal-conjectures` had no entry;
- the repository searches recorded in the issue found no earlier issue, module or Problems dossier for this conjecture.

The issue attributes the citation and external-search readings to search report `b16a6062aa6d7420947dd72d`. Its OpenAlex citing-work list request returned HTTP 429, so that citation check was limited to the DOI record. These reported searches are not an exhaustive literature certification: `not-found-in-searched-scope`.

## Route

All unqualified local lemma names below refer to the canonical module, including its private helpers.

1. **Reduced matrices for bipartite graphs.** For arbitrary natural $m,n$, Boolean biadjacency matrix $N$ of size $m\times n$, real $P$, and Boolean basis assignments $a,a'$ on $m$ bits and $b,b'$ on $n$ bits, put $t=2P-1$. The lemmas `reduced_A` and `reduced_B` give

   $\rho_A(a,a')=2^{-m}t^{d_H(a,a')}\mathbf1_{N^{\mathsf T}(a\oplus a')=0}$,

   $\rho_B(b,b')=2^{-n}t^{d_H(b,b')}\mathbf1_{N(b\oplus b')=0}$,

   with the kernel equations over $\mathbb F_2$. Here the graph is exactly `bipartiteGraph N`, with no edges within either part. These lemmas impose no probability-range or nonzero-rank hypothesis. Their character cancellation is `character_sum`: for natural $n$ and $k:\mathrm{Fin}\,n\to\mathbb N$, summing $\prod_j(-1)^{k_jb_j}$ over all Boolean $b$ gives $2^n$ if every $k_j$ is even, and zero otherwise.

2. **The fixed witness.** Take $m=5$, $n=4$, $P=255/256$ and

   $M=\begin{pmatrix}1&1&0&0\\1&1&0&0\\1&1&0&0\\1&0&1&0\\1&0&0&1\end{pmatrix}$.

   Set $u=(127/128)^2$, $a_1=(1+3u)/32$, $a_2=(1-u)/32$, $b_1=(1+u^2)/16$, and $b_2=(1-u^2)/16$. Let $Q_A(a,a')=1/4$ when $M^{\mathsf T}(a\oplus a')=0$ and zero otherwise, and let $Q_B=(I+F)/2$, where $F$ complements all four bits. For these fixed matrices, `projectionA_is_projection`, `projectionB_is_projection` and `projection_traces` establish that both are Hermitian projections with trace eight. At precisely this graph and probability, `marginal_A_spectral` and `marginal_B_spectral` give

   $\rho_A=a_1Q_A+a_2(I-Q_A)$, $\rho_B=b_1Q_B+b_2(I-Q_B)$.

3. **Entropy from projections.** For a finite index type with decidable equality, a square complex matrix $Q$ satisfying `IsStarProjection (CStarMatrix.ofMatrix Q)`, and arbitrary real $r,s$, `two_projection_entropy` gives

   $H\bigl(rQ+s(I-Q)\bigr)=\dfrac{-\operatorname{Re}\operatorname{Tr}(Q)\,r\log r-(d-\operatorname{Re}\operatorname{Tr}(Q))\,s\log s}{\log2}$,

   where $d$ is the cardinality of the index type and $H$ here denotes the module's `entropy2` extension. This uses `FullwoodParzygnatSubadditivityRefutation.projection_cfc` with $Q$ Hermitian and $Q^2=Q$. No positivity assumption on $r,s$ is needed for that formal extension. Applied only to the fixed witness above, `witness_entropies` gives

   $H(\rho_A)=\dfrac{-8a_1\log a_1-24a_2\log a_2}{\log2}$, $H(\rho_B)=\dfrac{-8b_1\log b_1-8b_2\log b_2}{\log2}$.

4. **Exact comparison.** For the fixed coefficients above, `numerical_inequality` establishes the strict comparison of the two entropy numerators using rational arithmetic and logarithm inequalities. It uses $1-1/x\le\log x\le x-1$ for positive $x$, the checked bounds $0<1-u\le1/64$ and $0<1+u\le2$, and $\log2<9/10$. The lemma `witness_entropy_comparison` divides by the positive $\log2$ to give $H(\rho_A)<H(\rho_B)$ at this witness. The theorem `result` applies `claim` at $4<5$ and $255/256\in[0,1]$ and cancels the same joint entropy from both sides to obtain a contradiction.

## Falsifier

The refutation would miss the source's conjecture if it used a different noise model, entropy, marginal or direction of coherent information. The correspondence is explicit:

- `noisyQubit` is the mixture of the normalized one-qubit plus and minus outer products with weights $P$ and $1-P$;
- `czPhase` multiplies the diagonal controlled-Z entry over every graph edge, and `graphState` conjugates the product of the one-qubit matrix entries by those phases;
- `partialTraceRight` sums over the second basis index, giving $\rho_A$; `partialTraceLeft` sums over the first, giving $\rho_B$;
- `entropy2` is $-\operatorname{Re}\operatorname{Tr}(\rho\,\mathrm{CFC.log}(\rho))/\log2$, using `CStarMatrix.ofMatrix`. It is defined on all finite square complex matrices, rather than taking a density-matrix proof as an argument;
- `coherentInfoA` and `coherentInfoB` subtract the same joint entropy from the respective marginal entropy, exactly as in the source's §2.3.

The witness uses the source's uniform independent noise and $P=255/256$, which also lies in the depolarization-compatible range $[1/2,1]$. Its density-matrix interpretation is justified in the unformalized argument below; the module does not expose a separate positivity-and-trace-one theorem for `graphState`.

## Evidence

The canonical source is `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.lean` (511 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.lean.json`, statement `sha256:c1274a1f6223d04bb8175edf04c73fa6e7180ea7609ccb21c98a513ad24052f3`.

Declaration statements:

- `result`: `sha256:99eaf17302bfaa9f883ab776228d9cc63e79117a38097f5a56b26e8388d789e3`;
- `claim`: `sha256:0fec2dfdffa1a56bd16aadb3d53d4b77365193670955e76d146ab08e5f7f8a0e`.

## Triage

Tier 1: an explicit conjecture of a 2024 e-print retained in its 2026 journal version, supported there by examples; preregistered in issue #21154 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that for every pair of natural subsystem sizes with $n_B<n_A$, every simple graph on their disjoint union with decidable adjacency, and every common $P\in[0,1]$, the module's coherent information on $B$ is at most that on $A$.

**Argued, not formalized.**

- *Physical admissibility.* The vectors $\lvert+\rangle$ and $\lvert-\rangle$ form an orthonormal basis, so $\sigma_P$ has eigenvalues $P$ and $1-P$. For $P\in[0,1]$ it is positive semidefinite with trace one. Tensor products preserve these properties. Each controlled-Z phase is $1$ or $-1$, so the diagonal product $U_G$ is unitary and preserves positivity and trace under conjugation. Thus the displayed witness is a physical density matrix. On its positive marginal eigenvalues the functional-calculus logarithm is the ordinary spectral logarithm.
- *Mechanism and nearby noise parameters.* Cardinalities do not determine the weights of binary dependencies. For this matrix the three nonzero vectors in $\ker M^{\mathsf T}$ have weight two, whereas the sole nonzero vector in $\ker M$ has weight four. The generic formulas of `reduced_A` and `reduced_B`, for arbitrary real $P$ and this fixed bipartite matrix, therefore give constant off-diagonal entries $t^2/32$ within each four-element $A$ coset and $t^4/16$ within each complementary pair on $B$. Consequently the same projection decompositions follow algebraically with $u=t^2$; the module's named spectral lemmas themselves state only the fixed probability. Put $\varepsilon=1-P\downarrow0$. Then $a_2=\varepsilon/8+O(\varepsilon^2)$ and $b_2=\varepsilon/2+O(\varepsilon^2)$, so the total eigenvalue mass emerging from zero is $3\varepsilon+O(\varepsilon^2)$ on $A$ and $4\varepsilon+O(\varepsilon^2)$ on $B$. The eight eigenvalues on each side that remain positive in the noiseless limit tend to $1/8$ and contribute $3+O(\varepsilon)$ to entropy; the small eigenvalues contribute the respective leading terms $3\varepsilon\log_2(1/\varepsilon)$ and $4\varepsilon\log_2(1/\varepsilon)$. Thus $H(\rho_B)-H(\rho_A)=\varepsilon\log_2(1/\varepsilon)+O(\varepsilon)>0$ for sufficiently small positive $\varepsilon$. This asymptotic argument supplies no explicit interval and is not a theorem of the module.
- *Restricted statements that survive.* For a bipartite graph with binary rank $r=n_B\le n_A$ and $P\in[0,1]$, the smaller side has zero kernel and hence $\rho_B=I/2^r$. The source's entropy decomposition in §4, `main.tex` lines 529–533, writes $H(\rho_A)=r+H(w_A)$ for its probability vector of orthogonal stabilizer sectors. Nonnegativity of Shannon entropy gives $H(\rho_A)\ge r=H(\rho_B)$, so the non-strict ordering survives this additional full-rank condition on the smaller side. The witness has $r=3<4$ and does not meet that condition. The source's complete bipartite case also retains the non-strict ordering: for $n_A\ge n_B\ge1$ and common $P\in[0,1]$, its §4.3 weights are the distribution of $(E_1\oplus E_2,\ldots,E_1\oplus E_n)$ for independent Bernoulli error bits with error probability $1-P$. Their entropy, plus one, is the subsystem entropy. The shorter vector is a marginal of the longer one, so its Shannon entropy cannot be larger. This argument is for the all-ones biadjacency matrix, without extra vertices lacking cross edges. At $P=0$ or $P=1$ the joint state is pure, so the marginal entropies agree.
- *Effect on the paper.* The general ordering conjectured in §5.4 and motivated by the observations in the “Properties” paragraph at `main.tex` line 861 cannot justify choosing a coherent-information direction by qubit count. The source's prescription to compare $\mathcal I_A$ and $\mathcal I_B$ remains applicable; at the witness the smaller side supplies the larger lower bound. The counterexample does not contradict the entropy algorithm, the separate complete bipartite or full-rank cases in §5.4, or the rank-one and rank-two calculations, since its binary rank is three. It does not settle a universal rank-two ordering, the separate higher-rank robustness conjecture in §5.3, or the extensions to other noise models raised in the conclusion. It compares entropy-based lower bounds, rather than asserting a reversal of operational distillation rates.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The OpenAlex citation record and incomplete citing-work list, arXiv title and author searches, MathDB and `google-deepmind/formal-conjectures` checks, reading of Goodenough et al. (2024 preprint), arXiv:2406.02427v2, and repository-wide absence search are reported in #21154 and are not independently reproduced here. The issue's orchestrator reports a grid scan near $P=1$; that scan is not reproduced, and no interval claim is taken from it.

The physical-admissibility reasoning, asymptotic extension, surviving restricted orderings and consequences discussed under “Argued, not formalized” are outside the statement of `result`. The dossier supplies neither a formal noise interval nor a formal classification of the graphs for which the ordering survives.
