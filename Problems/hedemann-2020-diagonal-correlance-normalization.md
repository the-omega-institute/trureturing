---
slug: hedemann-2020-diagonal-correlance-normalization
bibkey: hedemann2020correlance
doi: 10.1007/s11128-020-02676-8
url: https://arxiv.org/abs/2001.03453v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.result
---

# Hedemann's proposed diagonal-correlance normalization is exceeded by seven qubits

## Problem

Samuel R. Hedemann, *Correlance and Discordance: Computable Measures of Nonlocal Correlation*, Quantum Information Processing 19, 189 (2020), arXiv:2001.03453v2, Section II.C, defines the normalization as the maximum of raw correlance over all diagonal states in Eq. (16), and states:

> Instead, one simple example that maximizes $\mathcal{X}_D$ in all systems is
> $\rho_{D_{\max}}=\frac{1}{2}(|1\rangle\langle1|+|n\rangle\langle n|),$
> yielding the normalization factor, valid for all systems,
> $\mathcal{N}_{\mathcal{X}_D}=\widetilde{\mathcal{X}}(\rho_{D_{\text{max}}})=\frac{1}{2}-\frac{1}{2^N}.$

This quotation is from `CorrelanceAndDiscordance.tex`, lines 456–465, Eqs. (17)–(18); mathematical macros are expanded and layout commands omitted. Here $N$ is the number of modes and $n$ is their total Hilbert-space dimension. Appendix L, Step 9, line 2385, acknowledges:

> However, a rigorous proof of this is still lacking.

For $N$ qubits, write a diagonal state as $\rho=\operatorname{diag}(p)$ with $p:\{0,1\}^N\to\mathbb{R}$, $p(x)\ge0$ and $\sum_xp(x)=1$. Put $m_i(b)=\sum_{x:x_i=b}p(x)$ and $q(x)=\prod_i m_i(x_i)$. The source's raw correlance and reduction product, Eqs. (10)–(11), become
$R_N(p)=\operatorname{tr}[(\operatorname{diag}(p)-\operatorname{diag}(q))^2]=\sum_x(p(x)-q(x))^2$.

Issue [#22752](https://github.com/the-omega-institute/trureturing/issues/22752) fixes the qubit consequence of the source's assertion: for every natural $N\ge2$ and every such probability table, $R_N(p)\le\frac12-2^{-N}$. This universal bound is refuted.

## Motivation

Diagonal correlance is intended to normalize correlation in classical probability distributions and diagonal quantum states against the largest value available within that class. A normalization below an attainable value permits diagonal correlance above one. The same proposed maximum also enters the threshold for strong discordance in the source's Section V.A, so its interpretation depends on this optimization.

## Gap

The bounded literature check in #22752 records:

- The v2 source retains the universal normalization and explicitly acknowledges the missing rigorous proof; its Conclusion repeats the request for a more explicit proof (TeX line 1420).
- The search-fr reading reports seven citing works listed by OpenAlex and INSPIRE, with no correction found in the full texts of Hedemann's arXiv:2109.11548v2, 2208.04745v1 and 2506.02036v2; the other four were checked only at abstract or preview level.
- The same reported reading found no match in MathDB or formal-conjectures.
- The orchestrator's repository searches found no existing settlement of this assertion; issue #18345 concerns a different paper and problem.

`not-found-in-searched-scope`.

## Route

The module's local helper lemmas named below are private.

1. **The diagonal identity.** For every natural $N$ and every real table $p:(\mathrm{Fin}\,N\to\mathrm{Bool})\to\mathbb{R}$, with no probability hypothesis, `correlanceRaw_eq_sum` identifies `correlanceRaw p` with $\sum_x(p(x)-\prod_i m_i(x_i))^2$. The definitions `reductionProduct` and `correlanceRaw` use real diagonal matrices and their matrix trace; `FunOnFinite.map` supplies the coordinate-fiber sums.
2. **The seven-qubit table.** `witness` assigns $3/5$ to the all-false string, $2/5$ to the all-true string and zero elsewhere. `witness_probability` establishes nonnegativity and total mass one. For every $i:\mathrm{Fin}\,7$ and every Boolean $b$, `witness_marginal` gives marginal mass $3/5$ at false and $2/5$ at true; `witness_product` substitutes these marginals for every seven-bit string.
3. **The exact evaluation.** For this fixed seven-bit witness and these fixed weights, `sum_witness_square` gives $\sum_xp(x)^2=13/25$, `sum_witness_product` gives $\sum_xp(x)q(x)=(3/5)^8+(2/5)^8$, and `sum_product_q_square` gives $\sum_xq(x)^2=(13/25)^7$, using `Fintype.prod_sum`. Expanding the squared difference, `witness_raw` concludes $R_7(p)=3023545392/6103515625$.
4. **Contradiction.** `result` applies `claim` to $N=7$, the fact $2\le7$ and `witness_probability`. Exact arithmetic contradicts the resulting bound $R_7(p)\le63/128$; the excess is $2492325801/781250000000>0$.

## Falsifier

The refutation would not answer the source if the coordinate sums represented a different reduction product, or if the witness were not a probability table. A diagonal matrix with nonnegative entries is positive semidefinite, and its trace is their sum. Its one-qubit reduced matrices have entries $m_i(b)$, and their tensor product has diagonal entries $q(x)$. Thus the real diagonal-matrix encoding has exactly the source's raw correlance on the qubit states at issue. The complex density-matrix and partial-trace identifications in this explanation are not separate declarations of the module.

The source's Figure 4 caption (TeX line 476) describes tests of systems with at most $n=18$ total levels and 30,000 states per system. Seven qubits have $n=128$ levels, outside that stated range. Those tests therefore do not include this counterexample.

## Evidence

The canonical source is `D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`, where `claim : Prop` is the universal probability-table bound above.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:af6a1edf5ad5708f3a8dfc03b5b99b89c694d9895d321a58a804fdd02a172bee`;
- `claim`: `sha256:c5150e7e437d8ad39a923ec469ed9c8fea3091f002dbdb7d0c932d1deea1af13`.

## Triage

Tier 1 explicitly unproved normalization assertion of a 2020 paper, preregistered in issue #22752 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every natural $N\ge2$ and every nonnegative real probability table on $N$-bit strings with total mass one, `correlanceRaw` is at most $\frac12-2^{-N}$.

**Computed, not formalized:** an exact rational recomputation of the witness by the orchestrator and the dossier seat agrees with `result`, and a grid scan of two-point endpoint mixtures found values above the proposed bound for seven and eight qubits and none for two to six.

**Argued, not formalized.**

- *Mechanism and the missing optimization.* For $N\ge2$ and $0\le a\le1$, the endpoint mixture with masses $a$ and $1-a$ has parent purity $a^2+(1-a)^2$, reduction-product purity $(a^2+(1-a)^2)^N$, and overlap $a^{N+1}+(1-a)^{N+1}$. This follows by taking its identical coordinate marginals and factoring the sum of squared product entries. Consequently its raw value is the parent purity plus the reduction-product purity minus twice the overlap. These three quantities vary together. The source's Appendix L, Step 9, asserts that balancing the two weights maximizes their combination, but `witness_raw` supplies the contrary value at $N=7$ for the fixed weights $3/5,2/5$; Step 10's equal-weight conclusion cannot supply a universal maximizer. A rank-two or endpoint-support restriction alone does not remove this counterexample.
- *Statements that survive.* At $a=1/2$ and every $N\ge2$, the parent purity is $1/2$, the reduction product is uniform on $2^N$ strings, and its purity and overlap are both $2^{-N}$, giving exactly $\frac12-2^{-N}$. Thus the value computed for the source's candidate remains correct, without its claimed maximality. For a product of one-coordinate probability tables, each marginal is its corresponding factor, so $q=p$ and raw correlance is zero. The value of the true diagonal maximum, and the universal bound for all tables at each $N=2,\ldots,6$, remain open here; the finite grid check settles neither question.
- *Effect on dependent source statements.* Equations (15) and (18) together permit diagonal correlance above one at the witness. In Section V.A, Eqs. (34)–(35) substitute this same proposed diagonal maximum into strong discordance. For $N\ge2$ qubits, Eq. (14) supplies $\mathcal{N}_{\mathcal{X}}=1-2^{-N}$, so Eq. (35) reduces algebraically to $2\max\{0,R_N(p)-(\frac12-2^{-N})\}$. Its positive value on the diagonal witness contradicts its stated interpretation as correlation beyond that achievable by a strictly classical state. The definition in Eq. (33), when its threshold is an actual diagonal maximum, requires a corrected maximum to obtain that interpretation. Appendix L's classification of all maximizers by local permutations of the balanced candidate also cannot be complete: such permutations only relabel the sum and its marginals, preserving the candidate's smaller value. These conclusions concern the use of the proposed diagonal maximum; `result` does not settle the source's general correlance normalization or its other measures.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The citing-work readings, OpenAlex and INSPIRE counts, MathDB and formal-conjectures searches, source-version-history reading and repository deduplication reported in #22752 were not independently reproduced here; four citing works were read only at abstract or preview level in that reported check. The Crossref metadata verification recorded there was not repeated. The v2 TeX passages quoted and used above were read directly.

The statements labelled "Computed, not formalized" and "Argued, not formalized", including the density-matrix interpretation, surviving special cases and effects on strong discordance, are not additional Lean theorems. No true diagonal maximum, exhaustive small-mode optimization, or correction of the source's other measures is established by the module. The source's random-state tests and combinatorial experiments were not reproduced, and the general correlance normalization of Eq. (14) used in the strong-discordance argument is taken from the source rather than independently verified.
