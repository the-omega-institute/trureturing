---
slug: stratton-hsieh-skrzypczyk-2025-bound-coherence-higher-dimensions
bibkey: strattonhsiehskrzypczyk2026concentration
doi: 10.1103/fj8w-v1bb
url: https://arxiv.org/abs/2512.04255v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.result
---

# Bound-coherent states exist in every dimension at least three

## Problem

B. Stratton, C.-Y. Hsieh and P. Skrzypczyk, *Unspeakable coherence concentration*, arXiv:2512.04255v1 (2025), published as Phys. Rev. A 113, 062429 (2026), Section IX, Discussion, `main.tex` line 387:

> Finally, a family of states with bound-coherence was shown to exist, i.e., states that are not maximally coherent, nor incoherent, but for which no allowed unitary exists to perform coherence concentration. We leave it open to determine if such states exist in higher dimensions.

Issue [#22599](https://github.com/the-omega-institute/trureturing/issues/22599) fixes the reading for two identical copies with the truncated number observable $L=\sum_{n=0}^{d-1}n|n\rangle\langle n|$. For every integer $d\ge3$, there is a positive semidefinite matrix $\rho$ of trace one with $[\rho,L]\ne0$, which is not an equal-amplitude pure state, such that for every unitary $V$ commuting with $L\otimes I+I\otimes L$,

$M^{(j)}\bigl(\operatorname{tr}_B[V(\rho\otimes\rho)V^\dagger]\bigr)\le M^{(j)}(\rho)\quad(1\le j\le d-1).$

Here $\rho^{(j)}$ retains the entries with row number minus column number equal to $j$, and $M^{(j)}(\rho)=\|\rho^{(j)}\|_1$. An equal-amplitude pure state means $|\psi\rangle\langle\psi|$ with $\psi_n=e^{i\theta_n}/\sqrt d$ for real phases $\theta_n$. This reading is proved. The source definitions and their locators are in [the literature note](../Library/Eigenstructure/strattonhsiehskrzypczyk2026concentration.md).

## Motivation

The question distinguishes having coherence from being able to concentrate it through a number-conserving interaction of two copies. Examples in every dimension show that nonzero, nonmaximal coherence alone cannot guarantee an increase in even one positive mode. The restriction to two identical copies, the first output marginal and the specified observable is part of the conclusion.

## Gap

Issue #22599 records the bounded literature check before any Lean:

- the v1 TeX contains the quoted higher-dimensional question;
- the orchestrator's repository search found no existing issue, module, literature note or dossier for arXiv:2512.04255;
- the search seat reported title, quotation and author/keyword searches restricted to Zenodo, ResearchGate, SSRN and GitHub, finding no settlement, and reported that the authors' GitHub repository contained figure code only.

`not-found-in-searched-scope`.

## Route

Fix $d\ge3$, put $D=d-1$, and take the module's `witness`:

$\rho_d=\dfrac1d\bigl(I+|D\rangle\langle0|+|0\rangle\langle D|\bigr).$

All witness lemmas below have the hypothesis $d\ge3$. Every occurrence of an allowed $V$ means both unitarity and commutation with $L\otimes I+I\otimes L$.

1. **The state.** `witness_posSemidef` writes $\rho_d=d^{-1}(uu^\dagger+\operatorname{diag}(f))$, where $u=|0\rangle+|D\rangle$, and $f$ is zero at the endpoints and one elsewhere. `witness_trace` gives trace one. `witness_coherent` separates the $(D,0)$ entries of $\rho_dL$ and $L\rho_d$, namely zero and $D/d$. `witness_not_maximal` uses $\rho_d(0,1)=0$, whereas the corresponding entry of every equal-amplitude pure state is nonzero.
2. **Conservation of total number.** For any natural dimension $d$, any allowed $V$, and product-basis indices $a,b$ with $a_1+a_2\ne b_1+b_2$, `allowed_entry_zero` gives $V_{a,b}=0$. For $d\ge3$, indices $a,b$, and a natural $j$ with $1\le j<D$ and $a_1+a_2=b_1+b_2+j$, `tensor_gap_zero` gives $(\rho_d\otimes\rho_d)_{a,b}=0$. Consequently, for $d\ge3$, allowed $V$ and $1\le j<D$, `concentrated_lower_mode` says the entire $j$th output mode vanishes.
3. **The top-mode entry.** For $d\ge3$ and allowed $V$, `concentrated_last_entry` gives $q=\sigma_A(D,0)=d^{-2}\sum_{k=0}^{D}t_k$, where

   $t_k=V_{(D,k),(D,k)}\overline{V_{(0,k),(0,k)}}+V_{(D,k),(k,D)}\overline{V_{(0,k),(k,0)}}.$

   For $d\ge3$, allowed $V$ and $k\in\{0,\ldots,D\}$ with $k\ne0$ and $k\ne D$, `interior_term_bound` gives $|t_k|\le1$ by the two selected row norms and Cauchy–Schwarz. For $d\ge3$ and allowed $V$, `endpoint_terms_bound` gives $|t_0|+|t_D|\le2$: the columns indexed by $(D,0)$ and $(0,D)$ are orthonormal, so their sum has squared norm two; its two selected coordinates have squared moduli summing to at most two, and the remaining diagonal factors have modulus at most one. With $d-2$ interior terms, `concentrated_last_entry_bound`, for $d\ge3$ and allowed $V$, concludes $|q|\le1/d$.
4. **Comparison of modes.** For $d\ge3$ and any complex $d\times d$ matrix $x$, `last_mode_traceNorm` identifies $M^{(D)}(x)$ with $|x(D,0)|$. For $d\ge3$, `witness_last_coherence` gives $M^{(D)}(\rho_d)=1/d$. Thus `witness_no_concentration`, for $d\ge3$, allowed $V$ and each natural $j$ with $1\le j\le D$, gives the required comparison, using the vanishing output mode and nonnegativity of the input trace norm when $j<D$. These facts supply the existential state in `result : claim`.

## Falsifier

A mismatch between the operational reading and the formal definitions would invalidate the settlement. The module defines `IsAllowedUnitary` by membership in the complex matrix unitary group together with the exact total-number commutator, `concentrated` by conjugating two identical copies and tracing out the second factor, and `mode` by the signed integer difference of the two basis indices. `IsMaximallyCoherent` is precisely the equal-amplitude pure-state predicate specified above.

The imported trace norm is $\operatorname{Re}\operatorname{tr}\sqrt{x^\dagger x}$; the source's Section IV, `main.tex` line 261, uses the convention $\operatorname{tr}\sqrt{PP^\dagger}$. These agree because $x^\dagger x$ and $xx^\dagger$ have the same singular-value squares. The imported right partial trace has entries $\sum_k X_{(r,k),(s,k)}$. The claim quantifies over every allowed unitary and every positive local mode; it does not encode an optimization using an infimum or supremum, or infer the conclusion from sampling.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.lean.json`.

Declaration statements:

- `result`: `sha256:4ff1a804e3d29815fbc7992075a6b1eeb7457fe51418bad319fb1e70bc3f52f6`;
- `claim`: `sha256:a6aa204e0a612183c89b52c50910a4a6c7e224a331920a6dba614318a018cf91`.

## Triage

Tier 1 question of a 2025 preprint published in Phys. Rev. A in 2026, preregistered in issue #22599 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural dimension $d\ge3$, there exists a positive semidefinite complex $d\times d$ matrix $\rho$ of trace one that does not commute with the truncated number observable, is not an equal-amplitude pure state, and satisfies $M^{(j)}(\sigma_A)\le M^{(j)}(\rho)$ for every allowed unitary acting on two identical copies and every natural mode $1\le j\le d-1$, with $\sigma_A$ the first marginal.

**Computed, not formalized** (orchestrator, recorded in #22599): for the single qutrit state tested with 20,000 random allowed unitaries, no increase in either positive local mode was observed.

**Argued, not formalized.**

- *Decisive mechanism.* For $d\ge3$ and allowed $V$, the proof separates two obligations: `concentrated_lower_mode` excludes every mode with $1\le j<D$, and `concentrated_last_entry_bound` controls the remaining entry for $\rho_d$. Mode preservation alone would leave the top-mode increase unconstrained. The joint endpoint estimate matters because both endpoint contributions use the same sum of two orthonormal columns; bounding them separately would lose that constraint.
- *Sharpness for the witness.* For every $d\ge3$, $V=I$ is allowed and $\operatorname{tr}_B(\rho_d\otimes\rho_d)=\rho_d\operatorname{tr}\rho_d=\rho_d$. It attains the initial coherence in every mode, including $1/d$ in mode $D$. Together with the universal comparison, this gives zero optimal gain, with an explicit maximizer. The same allowed identity simultaneously attains all the mode bounds.
- *Smaller endpoint coherence and full rank.* Fix $d\ge3$ and $0<c\le1/d$. The matrix $\rho_c=I/d+c(|D\rangle\langle0|+|0\rangle\langle D|)$ has eigenvalues $1/d+c$, $1/d-c$, and $1/d$ on the remaining $d-2$ basis directions. It is a state, is coherent since $cD\ne0$, and is not equal-amplitude pure because its $(0,1)$ entry is zero. Its tensor product has number differences only $0,\pm D,\pm2D$, and its positive $D$ component is $(c/d)(F\otimes I+I\otimes F)$, where $F=|D\rangle\langle0|$. Conservation therefore kills every positive local mode below $D$ and gives $q=(c/d)\sum_k t_k$ in mode $D$. For $d\ge3$ and allowed $V$, `interior_term_bound` applies to each $k\ne0,D$, and `endpoint_terms_bound` controls the two endpoints, giving $|\sum_k t_k|\le d$. Hence $|q|\le c=M^{(D)}(\rho_c)$. This extends the argument to every such $c$; when $c<1/d$, all the listed eigenvalues are positive, so the obstruction does not require a zero eigenvalue.
- *Boundaries and neighbouring questions.* The formal existence statement supplies neither a classification of bound-coherent states nor a conclusion for more than two copies, different observables, arbitrary coherence measures or general covariant channels. Those extensions remain open here. The witness's top mode is present, so absence of lower modes alone cannot certify its bound coherence.
- *Effect on the source.* The quoted question occurs in the Discussion and is not used there as a hypothesis for a downstream theorem. The settlement answers it affirmatively on the preregistered reading and supplies higher-dimensional examples for comparison with the source's upper bounds. It does not determine whether those upper bounds are tight or resolve the source's questions about more general concentration protocols.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The site-restricted searches and the contents of the authors' GitHub repository are the search seat's reports in #22599; those searches were not reproduced here. The journal publication metadata is recorded in the issue and literature note; the journal text and its retention of the question were not independently read. The quotation and operational definitions were checked against arXiv:2512.04255v1 `main.tex`.

The numerical experiment is the orchestrator's report in #22599 and was not reproduced here. The statements under “Argued, not formalized”, including sharpness and the full-rank family with smaller endpoint coherence, and the singular-value comparison of trace-norm conventions are outside the statement of `result`; these arguments have not been separately formalized. The more general balanced-population family described in #22599, its possible unbalanced extensions and all multi-copy or operation-class extensions remain outside this formal settlement. No global repository checks or admission checks are asserted here.
