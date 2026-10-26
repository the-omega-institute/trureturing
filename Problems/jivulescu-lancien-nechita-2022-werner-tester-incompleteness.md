---
slug: jivulescu-lancien-nechita-2022-werner-tester-incompleteness
bibkey: jivulescularciennechita2022testers
doi: 10.1007/s00023-022-01187-9
url: https://arxiv.org/abs/2010.06365v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.result
---

# Complex testers do not detect every entangled Werner state

## Problem

M. A. Jivulescu, C. Lancien and I. Nechita, *Multipartite Entanglement Detection Via Projective Tensor Norms*, arXiv:2010.06365v1 (Annales Henri Poincaré 23 (2022), 3791–3838), Section `sec:conclusions`, posed the following question in `main.tex`, line 1365:

> The main question that remains unanswered at this point is whether our family of entanglement criteria is complete, without allowing for permutation of indices before applying the testers. Concretely, we would like to know if, for any entangled state $\rho$ on $\mathbb C^{d_1}\otimes\cdots\otimes\mathbb C^{d_m}$, there exist testers $\mathcal E_i:S_1^{d_i}\to\ell_2^{n_i}$, $1\leq i\leq m$, such that $\|\mathcal E_1\otimes\cdots\otimes\mathcal E_m(\rho)\|_{\ell_2^{n_1}\otimes_\pi\cdots\otimes_\pi\ell_2^{n_m}}>1$. Even for bipartite states we are only able to show a weaker version of this statement (see Section \ref{sec:completeness}).

The source defines the projective tensor norm by the infimum of the sums of products of factor norms (Definition, `main.tex`, lines 234–238), the trace norm by $\|X\|_1=\operatorname{Tr}\sqrt{X^*X}$ (`main.tex`, lines 288–290), and a complex tester as a complex-linear map of norm exactly one from the Schatten-1 space to the Euclidean space (`main.tex`, lines 340–352). Its Werner state is
\[
\sigma_\mu=\mu\frac{I+F}{d(d+1)}+(1-\mu)\frac{I-F}{d(d-1)},\qquad 0\leq\mu\leq1
\]
(`main.tex`, line 946).

The Lean declaration `claim` is the bipartite instance. For every $d_1,d_2$, every matrix $\rho$ on $(\operatorname{Fin}d_1\times\operatorname{Fin}d_2)$ that is positive semidefinite, has trace $1$, and is not `Separable`, it requires natural output dimensions and complex-linear maps $e_1,e_2$ such that each `IsTester` holds and
\[
1<\operatorname{projNorm}(\operatorname{testerImage}(e_1,e_2,\rho)).
\]
Here `IsTester e` is exactly the conjunction $\forall x,\ \|e x\|\leq\operatorname{traceNorm}(x)$ and $\exists x,\ x\neq0\land\|e x\|=\operatorname{traceNorm}(x)$. The formal `Separable` predicate is membership in the real convex hull of tensor products of positive semidefinite trace-one matrices, and `projNorm` is the displayed $sInf$ over finite matrix decompositions in the module.

The settlement is the negation of this bipartite claim. The source's universal multipartite question is therefore already false at two parties.

## Motivation

The paper presents testers as a way to turn mixed-state entanglement detection into a projective norm calculation on Euclidean output spaces. It records that the realignment and SIC POVM testers detect Werner states exactly for $\mu<1/d$, while Werner states are entangled for $\mu<1/2$ (Section `sec:symmetric-states`, `main.tex`, lines 985–1006). For $d>2$, the interval $1/d\leq\mu<1/2$ therefore isolates entangled states that those two named testers miss. The completeness question asks whether some other pair of testers can always close that gap without permuting indices.

## Gap

The preregistration issue [#22210](https://github.com/the-omega-institute/trureturing/issues/22210) records a Tier 1 literature check before formalization. It read the arXiv v1 source, the eight citing works listed by Semantic Scholar, the 2024 IHP talk abstract, a web search, and the MathDB entry for the completeness question. No answer was found in that searched scope, and no repository module, Library note, or dossier had settled the question.

The formal gap is the universal claim above: a single entangled density matrix for which every pair of trace-norm contractions has projective image norm at most $1$ is enough to refute it.

## Route

The module follows a finite fourth-root design and a swap witness.

1. **Formal objects.** `IsTester`, `testerImage`, `projNorm`, `Separable`, `werner`, and `claim` are the definitions used by `result`. The `projNorm` infimum is handled by `projective_decomposition_bound`, whose hypotheses are a finite index type, two vector families, and the bounds $\sum_t\|a_t\|^2\leq1$ and $\sum_t\|b_t\|^2\leq1$; it constructs a finite decomposition and proves its nonnegative cost is at most $1$.

2. **The design.** For `hd : 0 < d`, `design_weight_sum hd` proves that the design weights sum to $1$, `design_density hd t` proves positivity and trace one for each design projector, `design_second_entry hd i j k l` proves the weighted second-entry identity for every $i,j,k,l:\operatorname{Fin}d$, and `design_first hd` proves the weighted mean is `designAverage d`. The theorem `design_second_moment` assumes `hd : 0 < d`, a complex-linear map $e$, and `h : \forall x, \|e x\|\leq\operatorname{traceNorm}(x)`; it concludes
\[
\|e(\operatorname{designAverage}d)\|^2+
\sum_t\operatorname{designWeight}(d,t)\|e(\operatorname{designCentered}(d,t))\|^2\leq1.
\]
The theorem `werner_decomposition` assumes only `hd : 1 < d` and expresses `werner d μ` as the mean tensor square minus `correlation d μ` times the weighted centered tensor squares.

3. **The range and the contraction bound.** `correlation_range` assumes `hd : 1 < d`, `hμ₀ : 1 / (d : ℝ) ≤ μ`, and `hμ₁ : μ < 1 / 2`; it proves $0\leq\operatorname{correlation}(d,\mu)\leq1$. `werner_bound` has the same three hypotheses and, for arbitrary $n_1,n_2$, arbitrary complex-linear maps $e_1,e_2$, and contraction hypotheses `h₁ : \forall x, ‖e₁ x‖ ≤ traceNorm x` and `h₂ : \forall x, ‖e₂ x‖ ≤ traceNorm x`, proves
\[
\operatorname{projNorm}(\operatorname{testerImage}(e_1,e_2,\operatorname{werner}(d,\mu)))\leq1.
\]
Its proof applies `tester_image_decomposition` and `projective_decomposition_bound` to the finite design decomposition. The contraction hypotheses are deliberately weaker than `IsTester`, so the bound also covers every tester.

4. **Density and entanglement.** `werner_density` assumes `hd : 1 < d`, `hμ₀ : 0 ≤ μ`, and `hμ₁ : μ ≤ 1`; it proves that `werner d μ` is positive semidefinite and has trace $1$. `separable_flip_nonneg` assumes `h : Separable ρ` for a matrix $\rho$ of equal local dimension $d$ and proves $0\leq\operatorname{flipReadout}(d,\rho)$. With `hd : 1 < d`, `werner_readout` computes the readout of `werner d μ` as $2\mu-1$. Consequently, `werner_entangled` assumes `hd : 1 < d` and `hμ : μ < 1 / 2` and proves $\neg\operatorname{Separable}(\operatorname{werner}(d,\mu))$.

5. **Family theorem and refutation.** `werner_family` assumes `hd : 3 ≤ d`, `hμ₀ : 1 / (d : ℝ) ≤ μ`, and `hμ₁ : μ < 1 / 2`; it returns positivity, trace one, nonseparability, and the uniform projective bound for every pair of maps satisfying the two contraction hypotheses. `result` applies this theorem at $d=3$ and $\mu=1/3$. If `claim` supplied two `IsTester` maps for that state, their contraction conjuncts would give a projective norm at most $1$, contradicting the strict inequality required by `claim`.

## Falsifier

The refutation would not match the source question if any of the following formal identifications changed: `IsTester` would have to cease expressing a trace-norm contraction attaining equality at a nonzero matrix; `testerImage` would have to differ from the tensor-product coordinate expansion of the two maps; `projNorm` would have to use a different finite-decomposition infimum; `Separable` would have to use a different real convex hull of product density matrices; or `werner` would have to differ from the symmetric/antisymmetric mixture above. It would also fail to refute the claim if `result` did not have the exact type $\neg\,\mathrm{claim}$.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.lean`.
Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.lean.json`.
Declaration statements:
- `result`: `sha256:6700eba07215c5acdbb8a3e612e434f2fabccee6ade6d5b92099e6e40aca2227`;
- `claim`: `sha256:1add7f0599ef32b325d44a73bb263c99bd4c6bc843e371386d00fef5dd38e97b`.

- **Proof.** The module proves `result : ¬ claim`; its supporting public theorem `werner_family` supplies the density, entanglement, and contraction-bound facts used by the refutation.
- **Axioms.** `#print axioms D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.result` reports only `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 open question of the 2022 journal article, preregistered in issue #22210 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** `claim` is false. In exact terms, it is false that for every pair of natural local dimensions and every positive semidefinite trace-one matrix that is not `Separable`, there exist natural output dimensions and complex-linear maps satisfying `IsTester` on both sides and having
\[
1<\operatorname{projNorm}(\operatorname{testerImage}(e_1,e_2,\rho)).
\]

**Computed, not formalized.** The preregistration issue's orchestrator report records that the upper bound is attained by trace maps, so the supremum over testers is exactly $1$ for every $d\ge3$ and $\mu\in[1/d,1/2)$.

**Argued, not formalized.**
- **Mechanism of failure.** The supporting theorem `werner_family` identifies the missing structure: on the interval $1/d\leq\mu<1/2$, the Werner matrix is entangled while every pair of trace-norm contractions has image projective norm at most $1$. The finite fourth-root design supplies a common centered second-moment decomposition, and the weighted Cauchy–Schwarz estimate controls both output families. This explains why choosing larger output dimensions or requiring exact norm attainment cannot rescue the unpermuted criterion for this family.
- **Nearby statements.** The formal refutation uses the qutrit instance $(d,\mu)=(3,1/3)$; the supporting theorem covers all $d\ge3$ and $1/d\leq\mu<1/2$. It does not settle completeness after an index permutation, the source's separate statements about realignment or SIC POVM testers, or restricted variants of the tester class.
- **Effect on the source.** The source's positive result that every entangled bipartite mixed state can be detected after a permutation of indices, and its results for pure states and the named symmetric testers, do not assert `claim` and are unaffected. The unpermuted bipartite question is answered negatively, so the source's universal multipartite question is also false under its stated quantifiers because its two-party instance already fails. No theorem in the source is obtained here from assuming completeness.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources and searches recorded in issue #22210; it does not establish exhaustive worldwide novelty or priority. The journal full text was not read, so the direct source reading is arXiv v1 `main.tex` (md5 `9fdc54de5d2ae5f44ba87345810560e0`). The source's claims about realignment and SIC POVM detection, permutation-assisted detection, factorization through $\ell_2$, and the remaining multipartite directions are not formalized by this module. The trace-map attainment and exact supremum statement are recorded from the issue but are not formalized here. Interpretive statements about which nearby research questions remain open have not been independently settled beyond the bounded check.
