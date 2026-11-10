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
$\sigma_\mu=\mu\frac{I+F}{d(d+1)}+(1-\mu)\frac{I-F}{d(d-1)},\qquad 0\leq\mu\leq1$
(`main.tex`, line 946).

The Lean declaration `claim : Prop` is the bipartite instance. For every $d_1,d_2:\mathbb N$ and every $\rho:\operatorname{Matrix}(\operatorname{Fin}d_1\times\operatorname{Fin}d_2)(\operatorname{Fin}d_1\times\operatorname{Fin}d_2)\,\mathbb C$, its hypotheses are `ρ.PosSemidef`, `ρ.trace = 1`, and `¬ Separable ρ`; its conclusion requires $n_1,n_2:\mathbb N$ and complex-linear maps $e_i:\operatorname{Matrix}(\operatorname{Fin}d_i)(\operatorname{Fin}d_i)\,\mathbb C\to\operatorname{EuclideanSpace}\,\mathbb C\,(\operatorname{Fin}n_i)$ satisfying `IsTester e₁ ∧ IsTester e₂ ∧ 1 < ‖testerImage e₁ e₂ ρ‖`.

Here `IsTester e` is exactly the conjunction $\forall x,\ \|e x\|\leq\operatorname{traceNorm}(x)$ and $\exists x,\ x\neq0\land\|e x\|=\operatorname{traceNorm}(x)$. The formal `Separable` predicate is membership in the real convex hull of matrices `Matrix.kroneckerMap (· * ·) ρ₁ ρ₂`, where each factor is positive semidefinite with trace $1$.

The output of `testerImage` has type `⨂[ℂ] s : Bool, EuclideanSpace ℂ (Fin (cond s n₂ n₁))`: the `false` factor is the first Euclidean output space and the `true` factor is the second. Its norm $\|\cdot\|$ is Mathlib's bundled `PiTensorProduct.projectiveSeminorm` on this tensor product. This represents the source's $\ell_2^{n_1}\otimes_\pi\ell_2^{n_2}$ norm from `main.tex`, lines 234–238: the two factors carry their Euclidean norms, and each finite pure-tensor expansion has cost equal to the sum of the products of those factor norms. Mathlib permits explicit complex scalar coefficients in these expansions; absorbing each coefficient into either factor gives the source's convention, with the same cost. The tensor norm notation and application of `PiTensorProduct.projectiveSeminorm` are definitionally equal.

The settlement is the negation of this bipartite claim. The source's universal multipartite question is therefore already false at two parties.

## Motivation

The paper presents testers as a way to turn mixed-state entanglement detection into a projective norm calculation on Euclidean output spaces. It records that the realignment and SIC POVM testers detect Werner states exactly for $\mu<1/d$, while Werner states are entangled for $\mu<1/2$ (Section `sec:symmetric-states`, `main.tex`, lines 985–1006). For $d>2$, the interval $1/d\leq\mu<1/2$ therefore isolates entangled states that those two named testers miss. The completeness question asks whether some other pair of testers can always close that gap without permuting indices.

## Gap

The bounded Tier 1 literature check in issue [#22210](https://github.com/the-omega-institute/trureturing/issues/22210) covers the arXiv v1 source, the eight citing works listed by Semantic Scholar, the IHP talk abstract, a web search, and the MathDB entry for the completeness question. It identifies no answer within that scope; this is not an exhaustive novelty claim.

The formal gap is the universal claim above: a single entangled density matrix for which every pair of trace-norm contractions has projective image norm at most $1$ is enough to refute it.

## Route

The module follows a finite fourth-root design and a swap witness.

1. **Formal objects and the tensor estimate.** The public definitions are `IsTester`, `tensorPair`, `testerImage`, `Separable`, `werner`, and `claim`. For arbitrary $n_1,n_2:\mathbb N$, `tensorPair` is complex-linear in each of its two Euclidean arguments and returns `PiTensorProduct.tprod ℂ (Bool.rec a b)`. For arbitrary $d_1,d_2,n_1,n_2:\mathbb N$, maps $e_1,e_2$ of the types in `claim`, and a matrix $\rho$ of the corresponding product dimension, `testerImage e₁ e₂ ρ` is the tensor
   $\sum_{i,j,k,l}\rho_{(i,j),(k,l)}\,\operatorname{tensorPair}(e_1(\operatorname{Matrix.single}\ i\ k\ 1),e_2(\operatorname{Matrix.single}\ j\ l\ 1))$.
   The public `werner (d : ℕ) (μ : ℝ)` is the symmetric/antisymmetric mixture displayed in `Problem`, using the coordinate-swap permutation matrix for $F$; its definition imposes no range hypotheses.

   The private `tester_image_decomposition` has parameters `{d₁ d₂ n₁ n₂ : ℕ} {ι : Type*} [Fintype ι]`, the two complex-linear maps $e_1,e_2$, and matrix families $a:\iota\to\operatorname{Matrix}(\operatorname{Fin}d_1)(\operatorname{Fin}d_1)\,\mathbb C$ and $b:\iota\to\operatorname{Matrix}(\operatorname{Fin}d_2)(\operatorname{Fin}d_2)\,\mathbb C$. Without contraction hypotheses, it concludes
   $\operatorname{testerImage}(e_1,e_2,\sum_t\operatorname{Matrix.kroneckerMap}(\cdot*\cdot)(a_t)(b_t))=\sum_t\operatorname{tensorPair}(e_1(a_t),e_2(b_t))$.

   The private `projective_decomposition_bound` has parameters `{n₁ n₂ : ℕ} {ι : Type*} [Fintype ι]`, Euclidean vector families $a:\iota\to\operatorname{EuclideanSpace}\,\mathbb C\,(\operatorname{Fin}n_1)$ and $b:\iota\to\operatorname{EuclideanSpace}\,\mathbb C\,(\operatorname{Fin}n_2)$, and hypotheses `ha : ∑ t, ‖a t‖ ^ 2 ≤ 1` and `hb : ∑ t, ‖b t‖ ^ 2 ≤ 1`. Its conclusion is exactly `‖∑ t, tensorPair (a t) (b t)‖ ≤ 1`. Cauchy–Schwarz bounds the sum of products of norms; the triangle inequality and `PiTensorProduct.projectiveSeminorm_tprod_le` bound the tensor norm by that sum. The Mathlib theorem applies to a family $m$ in finitely many seminormed spaces over a normed field, each a normed space over that field, and concludes $\|\bigotimes_i m_i\|\leq\prod_i\|m_i\|$; here the field is $\mathbb C$ and the index type is `Bool`.

2. **The design.** All the design declarations and the decomposition theorem in this item are private. `DesignIndex (d : ℕ)` abbreviates `Fin d ⊕ (Fin d → Fin 4)`. Write $w_t=\operatorname{designWeight}\ d\ t$, $P_t=\operatorname{designProjector}\ d\ t$, $m=\operatorname{designAverage}\ d$, and $C_t=\operatorname{designCentered}\ d\ t$. The weights are $1/(d(d+1))$ on the basis indices and $d/((d+1)4^d)$ on the phase indices; the projectors are the corresponding basis projectors and $d^{-1}$ times the outer products of fourth-root phase vectors. The definitions give $m=d^{-1}I$ and $C_t=P_t-m$.

   For arbitrary `d : ℕ` and `t : DesignIndex d`, `design_weight_nonneg d t` concludes `0 ≤ designWeight d t`. With `{d : ℕ}` and `hd : 0 < d`, `design_weight_sum hd` concludes $\sum_t w_t=1$, `design_density hd t` concludes `(designProjector d t).PosSemidef ∧ (designProjector d t).trace = 1` for each `t : DesignIndex d`, and `design_first hd` concludes $\sum_t w_t\,P_t=m$. Under the same `hd`, for every `i j k l : Fin d`, `design_second_entry hd i j k l` concludes
   $\sum_t(w_t:\mathbb C)(P_t)_{ik}(P_t)_{jl}=\frac{1}{(d:\mathbb C)(d+1)}\bigl(\mathbf1_{i=k\,\land\,j=l}+\mathbf1_{i=l\,\land\,j=k}\bigr)$.

   The private `design_second_moment` has parameters `{d n : ℕ}`, `hd : 0 < d`, a complex-linear map $e:\operatorname{Matrix}(\operatorname{Fin}d)(\operatorname{Fin}d)\,\mathbb C\to\operatorname{EuclideanSpace}\,\mathbb C\,(\operatorname{Fin}n)$, and `h : ∀ x, ‖e x‖ ≤ traceNorm x`. Its conclusion is $\|e(m)\|^2+\sum_t w_t\|e(C_t)\|^2\leq1$.

   The private `correlation (d : ℕ) (μ : ℝ)` is $c=(d+1-2\mu d)/(d-1)$. The private `werner_decomposition` has parameters `{d : ℕ}`, `hd : 1 < d`, and arbitrary `μ : ℝ`; its conclusion is
   $\operatorname{werner}\ d\ \mu=\operatorname{Matrix.kroneckerMap}(\cdot*\cdot)(m)(m)-c\,\sum_t w_t\,\operatorname{Matrix.kroneckerMap}(\cdot*\cdot)(C_t)(C_t)$.

3. **The range and the contraction bound.** The private `correlation_range` has parameters `{d : ℕ} {μ : ℝ}` and hypotheses `hd : 1 < d`, `hμ₀ : 1 / (d : ℝ) ≤ μ`, and `hμ₁ : μ < 1 / 2`; its conclusion is `0 ≤ correlation d μ ∧ correlation d μ ≤ 1`. The private `werner_bound` has parameters `{d n₁ n₂ : ℕ} {μ : ℝ}`, the same three hypotheses, arbitrary complex-linear maps $e_i:\operatorname{Matrix}(\operatorname{Fin}d)(\operatorname{Fin}d)\,\mathbb C\to\operatorname{EuclideanSpace}\,\mathbb C\,(\operatorname{Fin}n_i)$, and `h₁ : ∀ x, ‖e₁ x‖ ≤ traceNorm x` and `h₂ : ∀ x, ‖e₂ x‖ ≤ traceNorm x`. Its conclusion is exactly `‖testerImage e₁ e₂ (werner d μ)‖ ≤ 1`. Its proof applies `tester_image_decomposition` and `projective_decomposition_bound` to the finite design decomposition. The contraction hypotheses follow from the first conjunct of each `IsTester` assumption, so the bound covers every tester.

4. **Density and entanglement.** The declarations in this item are private. For `{d : ℕ} {μ : ℝ}`, `werner_density` assumes `hd : 1 < d`, `hμ₀ : 0 ≤ μ`, and `hμ₁ : μ ≤ 1` and concludes `(werner d μ).PosSemidef ∧ (werner d μ).trace = 1`. The real-linear map `flipReadout (d : ℕ)` sends a matrix $\rho$ on `Fin d × Fin d` to $\operatorname{Re}\operatorname{Tr}(F\rho)$. With `{d : ℕ}`, such a matrix $\rho$, and `h : Separable ρ`, `separable_flip_nonneg ρ h` concludes `0 ≤ flipReadout d ρ`. With `{d : ℕ}`, `hd : 1 < d`, and arbitrary `μ : ℝ`, `werner_readout hd μ` concludes `flipReadout d (werner d μ) = 2 * μ - 1`. Finally, for `{d : ℕ} {μ : ℝ}`, `werner_entangled` assumes `hd : 1 < d` and `hμ : μ < 1 / 2` and concludes `¬ Separable (werner d μ)`.

5. **Family theorem and refutation.** The public `werner_family (d : ℕ) (μ : ℝ)` assumes `hd : 3 ≤ d`, `hμ₀ : 1 / (d : ℝ) ≤ μ`, and `hμ₁ : μ < 1 / 2`. Its conclusion is `(werner d μ).PosSemidef ∧ (werner d μ).trace = 1 ∧ ¬ Separable (werner d μ) ∧` the following universal bound: for every `n₁ n₂ : ℕ` and every complex-linear $e_i:\operatorname{Matrix}(\operatorname{Fin}d)(\operatorname{Fin}d)\,\mathbb C\to\operatorname{EuclideanSpace}\,\mathbb C\,(\operatorname{Fin}n_i)$, the hypotheses `∀ x, ‖e₁ x‖ ≤ traceNorm x` and `∀ x, ‖e₂ x‖ ≤ traceNorm x` imply `‖testerImage e₁ e₂ (werner d μ)‖ ≤ 1`. The public `result : ¬ claim` has no hypotheses. Its proof applies `werner_family` at $d=3$ and $\mu=1/3$; the contraction conjuncts of the two testers supplied by `claim` would contradict its required strict norm inequality.

## Falsifier

The source identification requires `IsTester` to express a trace-norm contraction attaining equality at a nonzero matrix; `tensorPair` to form the pure tensor of the two Euclidean outputs; `testerImage` to apply the two maps through the matrix-unit expansion into that `PiTensorProduct`; its bundled `PiTensorProduct.projectiveSeminorm`, written $\|\cdot\|$, to represent the source's Euclidean projective tensor norm; `Separable` to be the real convex hull of product density matrices; and `werner` to be the symmetric/antisymmetric mixture above. A mismatch in any of these identifications would invalidate the interpretation as a refutation of the source question. The compiled conclusion must be exactly `result : ¬ claim`; a norm estimate for a different tensor space or a different class of maps would not suffice.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.lean`.
Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.lean.json`.
Declaration statements:
- `result`: `sha256:6700eba07215c5acdbb8a3e612e434f2fabccee6ade6d5b92099e6e40aca2227`;
- `claim`: `sha256:1add7f0599ef32b325d44a73bb263c99bd4c6bc843e371386d00fef5dd38e97b`.

- **Proof.** The module proves `result : ¬ claim`; its supporting public theorem `werner_family` supplies the density, entanglement, and contraction-bound facts used by the refutation.
- **Axioms.** `#print axioms D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.result` reports only `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 open question of the cited journal article; literature scope is given in issue #22210.
`theorem`; resolution `refuted`.

The module uses the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result : ¬ claim`:** it is false that for every pair of natural local dimensions and every positive semidefinite trace-one matrix that is not `Separable`, there exist natural output dimensions and complex-linear maps satisfying `IsTester` on both sides and having $1<\|\operatorname{testerImage}(e_1,e_2,\rho)\|$ in the `Bool`-indexed tensor product of their Euclidean output spaces, with Mathlib's bundled projective norm.

**Computed, not formalized.** Issue #22210 reports trace-map attainment and an exact supremum over testers of $1$ for every $d\ge3$ and $\mu\in[1/d,1/2)$.

**Argued, not formalized.**

- **Mechanism of failure.** The supporting theorem `werner_family` identifies the missing structure: for $d\ge3$ and $1/d\leq\mu<1/2$, the Werner matrix is positive semidefinite with trace $1$ and is not `Separable`, while every pair of complex-linear maps satisfying the trace-norm contraction hypotheses has image projective norm at most $1$. The finite fourth-root design supplies a common centered second-moment decomposition, and the weighted Cauchy–Schwarz estimate controls both output families. This explains why choosing larger output dimensions or requiring exact norm attainment cannot rescue the unpermuted criterion for this family.
- **Nearby statements.** The formal refutation uses the qutrit instance $(d,\mu)=(3,1/3)$; the supporting theorem covers all $d\ge3$ and $1/d\leq\mu<1/2$. It does not settle completeness after an index permutation, the source's separate statements about realignment or SIC POVM testers, or restricted variants of the tester class.
- **Effect on the source.** The source's positive result that every entangled bipartite mixed state can be detected after a permutation of indices, and its results for pure states and the named symmetric testers, do not assert `claim` and are unaffected. The unpermuted bipartite question is answered negatively, so the source's universal multipartite question is also false under its stated quantifiers because its two-party instance already fails. No theorem in the source is obtained here from assuming completeness.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources and searches recorded in issue #22210; it does not establish exhaustive worldwide novelty or priority. The journal full text was not read, so the direct source reading is arXiv v1 `main.tex` (md5 `9fdc54de5d2ae5f44ba87345810560e0`). The source's claims about realignment and SIC POVM detection, permutation-assisted detection, factorization through $\ell_2$, and the remaining multipartite directions are not formalized by this module. The trace-map attainment and exact supremum statement are recorded from the issue but are not formalized here. Interpretive statements about which nearby research questions remain open have not been independently settled beyond the bounded check.
