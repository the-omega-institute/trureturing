---
slug: aksoy-et-al-2023-asynchronous-iteration-spectral-radius-refutation
bibkey: aksoyetal2023asynchrony
doi: 10.4310/JOC.2023.v14.n4.a8
url: https://arxiv.org/abs/2303.11464v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.result
---

# Both proposed spectral-radius bounds for asynchronous iteration are false

## Problem

S. G. Aksoy et al., *Seven open problems in applied combinatorics*, Journal of Combinatorics 14(4), 559–601 (2023), arXiv:2303.11464v1, includes the section “Price of Asynchrony” by Carlos Ortiz Marrero and Stephen J. Young. Its Open Problem reads:

> Let $M$ be a $n \times n$ real matrix with $p(M)= \lambda < 1$ partitioned into an $\ell \times \ell$ array of blocks.  Is it the case that for all elements $\delta$ of $[k]^{\ell \times \ell}$ with zero diagonals, $\rho(M^{(\delta)}) \leq \lambda^{\nicefrac{1}{k+1}}?$  If not, is there some function $f \colon (0,1) \times \N \rightarrow (0,1)$ such that $\rho(M^{(\delta)}) \leq f(\lambda,k)$?

This quotation is from the downloaded v1 TeX, `Sections/ratfish.tex`, lines 75–77, md5 `08f1f56ce6f899219ee74094fe3c0e53`. The surrounding model, lines 48–49, specifies:

> $\tilde{x}_i^{(k+1)} = \sum_j M_{ij}\tilde{x}_j^{(k - \delta_{ji})}$

and says “we assume that $\delta_{ii}=0$”. Here $p(M)$ in the question is read as the spectral radius $\rho(M)$ of that model. The operator $M^{(\delta,k)}$ acts on the newest iterate and its $k$ preceding iterates, updating the newest slot by this recurrence and shifting the remaining slots. The source uses $M^{(\delta)}$ for a history operator with enough slots (lines 51–62).

Issue [#21351](https://github.com/the-omega-institute/trureturing/issues/21351) fixes the formal reading: `claim` is `Q1 ∨ Q2`, where `Q1` is the universal power bound and `Q2` is the existence of the uniform bound strictly below one. Both alternatives are refuted, even with two scalar blocks, positive remote delays and $0<\lambda<1$. The source and its locator are also recorded in [the literature note](../Library/Eigenstructure/aksoyetal2023asynchrony.md).

## Motivation

The section asks how communication delays change the convergence of distributed linear iterations. A bound below one would guarantee spectral stability of the delayed iteration from the synchronous spectral radius and the delay bound alone. The witness instead has synchronous spectral radius $1/2$ and a delayed eigenvalue $5/4$: bounded communication delay can destroy spectral stability in the stated class of real matrices.

## Gap

The bounded literature check recorded in #21351 reports:

- the v1 source retains both questions;
- OpenAlex record W4365803326 listed one citing graph-learning paper, whose abstract was reported not to address this problem;
- the related asynchronous-iteration texts arXiv:1311.2121, 1411.2647, 2312.14715 and 2312.16505 were reported not to settle this fixed-delay question; the reported classical comparison conditions concern $\rho(|M|)$ and varying schedules;
- no entry was reported in MathDB or google-deepmind/formal-conjectures, and repository searches found no existing settlement of this source.

`not-found-in-searched-scope`. The external citation and database readings in that report have not been independently reproduced here.

## Route

Fix two blocks of size one, $k=1$, and

$$M=\begin{pmatrix}7/4&5/4\\-5/4&-3/4\end{pmatrix},\qquad
\delta=\begin{pmatrix}0&1\\1&0\end{pmatrix}.$$

In the order $(x_1(t),x_2(t),x_1(t-1),x_2(t-1))$, `asyncMatrix` gives

$$B=M^{(\delta,1)}=
\begin{pmatrix}7/4&0&0&5/4\\0&-3/4&-5/4&0\\1&0&0&0\\0&1&0&0\end{pmatrix}.$$

1. **Synchronous radius.** For this fixed matrix, `base_square_zero` proves $(M_{\mathbb C}-\tfrac12 I)^2=0$. Spectral translation and squaring give `base_spectrum`, namely $\operatorname{spec}_{\mathbb C}(M_{\mathbb C})=\{1/2\}$. The reverse inclusion uses noninvertibility of the nilpotent shift. `base_radius` therefore gives `radius M = ENNReal.ofReal (1 / 2)`.
2. **Admissibility.** `witness_admissible` establishes every condition of `Admissible` for these data: both block sizes are positive, diagonal delays are zero, all distinct-block delays lie between $1$ and $k=1$, $0<\lambda=1/2<1$, and the synchronous radius equals $\lambda$.
3. **Delayed radius.** `unstable_eigenvector` proves that $v=(10,-5,8,-4)$ is nonzero and $B_{\mathbb C}v=(5/4)v$. The reused `LaplacianGapMinDegree.eigenpair_mem_spectrum` requires a finite index type with decidable equality, a complex matrix, and a nonzero complex vector satisfying that eigenvector equation. These conditions hold for this four-coordinate matrix. `asynchronous_radius` uses the resulting spectrum member to prove $\operatorname{ENNReal.ofReal}(5/4)\le\operatorname{radius}(B)$ via the supremum in the extended nonnegative reals.
4. **Both contradictions.** For these admissible data, `not_q1` combines that lower bound with the proposed power bound. Its use of `Real.rpow_le_one` checks all three hypotheses: the base $1/2$ is nonnegative and at most one, and the exponent $1/(1+1)$ is nonnegative. Thus `Q1` would imply $5/4\le1$. In `not_q2`, the range requirement gives $0<f(1/2,1)<1$, while the proposed uniform bound gives $5/4\le f(1/2,1)$. `result` eliminates the disjunction of these two false alternatives.

## Falsifier

The counterexample must respect the source's block structure, delay convention and spectral radius. The module makes these choices explicit:

- Block coordinates are `Vtx n`, the dependent sum $\sum_{i:\mathrm{Fin}\,\ell}\mathrm{Fin}(n_i)$, with $n_i>0$ in `Admissible`. The witness has $\ell=2$ and $n_i=1$.
- History coordinates are $\mathrm{Fin}(k+1)\times\operatorname{Vtx}(n)$, with slot zero newest. An entry from block $j$ into block $i$ uses slot $\delta_{ji}$, exactly as in the quoted recurrence. The witness's delay array is symmetric, so reversing the two delay indices also leaves it unchanged.
- `radius` is Mathlib's `spectralRadius ℂ` of the entrywise complexification, with values in $\mathbb R_{\ge0}\cup\{\infty\}$. All comparisons in `Q1` and `Q2` use `ENNReal.ofReal`.
- The formal alternatives quantify over every natural $\ell$ and $k$, every block-size function, every real matrix on those block coordinates, every delay array, and every real $\lambda$, subject to `Admissible`. This predicate restricts remote delays to $1\le\delta_{ij}\le k$ and $\lambda$ to $(0,1)$. These restrictions suffice under either reading of the source's $[k]$: the positive remote-delay patterns are included whether zero remote delays are allowed or excluded.
- In `Q2`, $f:\mathbb R\to\mathbb N\to\mathbb R$ has $0<f(\lambda,k)<1$ for every $0<\lambda<1$ and every natural $k$; its values outside that interval are unrestricted. Extending a function on $(0,1)\times\mathbb N$ outside its original domain does not change either its bounds or the witness.

The result does not require a claim about every stable matrix or every delay pattern: one admissible counterexample negates each universal proposal.

## Evidence

The canonical source is `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.lean` (185 lines).

- **Proof.** It proves `result : ¬ claim`, with `claim : Prop` defined as `Q1 ∨ Q2`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.lean.json`, statement `sha256:9773c36a27c01ee9992c9a791d85908cef26909ddaa837675985c6cc5123ec70`.

Declaration statements:

- `result`: `sha256:1399bf20666d97e94914a0f172a4ca2524bfa7e33ef69a5750836e6cac583c45`;
- `claim`: `sha256:2390fdbe2d0ed93285a817b066333c652486156ff86164df182b80364fa8f7e9`.

## Triage

Tier 1 explicitly stated open problem of a 2023 survey, preregistered in issue #21351 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `result` | bind-only | none: the fixed nilpotent shift, eigenvector certificate, spectral lemmas and numerical contradictions instantiate existing results | open-problem-resolution |
| `asyncMatrix`, `radius`, `Admissible`, `Q1`, `Q2`, `claim` | bind-only | none | definitions used by `claim` |
| the fixed matrices, vector and certificate helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** neither the universal power bound `Q1` nor the existence assertion `Q2` holds for the admissible block matrices, delays and positive synchronous radii specified above. In particular, there is no function of $\lambda$ and $k$ alone, with values strictly between zero and one on $(0,1)\times\mathbb N$, that bounds the delayed radius for every such datum.

**Argued, not formalized.**

- *Mechanism.* The fixed synchronous matrix is $M=\tfrac12 I+N$ with $N=\tfrac54\begin{pmatrix}1&1\\-1&-1\end{pmatrix}$ and $N^2=0$, as certified for its complexification by `base_square_zero`. Thus its synchronous spectrum collapses to $\{1/2\}$ (`base_spectrum`) despite large signed entries. The delayed iteration keeps the diagonal action current while applying the off-diagonal action to the preceding iterate. The nilpotent cancellation no longer describes that history operator; `unstable_eigenvector` exhibits its expanding mode for precisely these data. Small synchronous spectral radius alone does not control this loss of cancellation.
- *A sufficient additional condition.* For a finite nonempty coordinate set, suppose $0<q<1$ and there is a vector $w$ with every $w_p>0$ and $\sum_j|M_{pj}|w_j\le q w_p$ for every coordinate $p$. Let every contributing delay lie between $0$ and $k$, and put $r=q^{1/(k+1)}$. On a history $y$, use $\|y\|_* =\max_{s,p}r^s|y_{s,p}|/w_p$. Its updated slot zero has weighted size at most $q r^{-k}\|y\|_*=r\|y\|_*$, since each source slot contributes at most $r^{-k}w_j\|y\|_*$. Every shifted slot also has weighted size at most $r\|y\|_*$. Applying this bound to a complex eigenvector gives $|z|\le r$, hence the delayed spectral radius is at most $r<1$. Taking $q=\lambda$ recovers the proposed power bound under this extra condition. The witness cannot satisfy this condition for any $q<1$, because its first absolute diagonal entry alone is $7/4$. This is a sufficient condition; a necessary characterization is not supplied.
- *Uniform delay remains a distinct case.* Lemma `L:uniform` has the hypothesis “$\delta_{ij} = k$ for all non-zero blocks of $M$” (`Sections/ratfish.tex`, line 67). If every contributing term is delayed exactly $k$, the history operator $C$ with $k+1$ slots satisfies $C^{k+1}=\operatorname{diag}(M,\ldots,M)$; spectral mapping gives $\rho(C)=\rho(M)^{1/(k+1)}$. This argument also covers zero eigenvalues. With zero local delays and $k>0$, that hypothesis requires zero diagonal blocks. The witness has nonzero diagonal blocks and therefore does not satisfy it. The formal module does not settle the proposed bound for all matrices with zero diagonal blocks.
- *Effect on the source.* The experimental discussion also mentions “the conjecture that $\rho(M^{(\delta)}) \leq \rho(M)^{\nicefrac{1}{\max \delta}}$” (line 148). At this witness $\max\delta=1$, so that alternative upper bound would be $1/2$, below the certified lower bound $5/4$. The conjectured bounds therefore cannot justify convergence in the unrestricted real-matrix model. The section contains no later theorem conditional on an affirmative answer to its Open Problem; its experimental observations and speculation about mean delays do not supply a replacement universal bound. The reported numerical experiments have not been reproduced here.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The OpenAlex citation count, the citing article's abstract, the four related arXiv readings, the classical asynchronous-iteration comparison literature, the MathDB and google-deepmind/formal-conjectures checks, and the preregistration's historical repository search are reports in #21351 rather than independently reproduced readings. No independent check of the complete arXiv version history is claimed.

The statements grouped under “Argued, not formalized” are not additional Lean conclusions. In particular, the weighted-history-norm repair, the uniformly delayed comparison, and the effect on the experimental variant are outside `result`'s formal statement. The complete delayed spectrum and the exact delayed radius are not identified by `result`. A necessary characterization of delay-robust stability and a universal power bound under the additional restriction of zero diagonal blocks are not settled by this module. The source's random-matrix plots and mean-delay comparisons were not reproduced.
