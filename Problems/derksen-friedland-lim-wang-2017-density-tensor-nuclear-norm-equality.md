---
slug: derksen-friedland-lim-wang-2017-density-tensor-nuclear-norm-equality
bibkey: derksenfriedlandlimwang2017entanglement
doi: 10.48550/arXiv.1705.07160
url: https://arxiv.org/abs/1705.07160v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.result
---

# A mixed density tensor attains the nuclear-norm maximum

## Problem

H. Derksen, S. Friedland, L.-H. Lim and L. Wang, *Theoretical and computational aspects of entanglement* (2017), arXiv:1705.07160v1, §6, immediately following Lemma 6.2, conjecture:

> We conjecture that equality in (6.4) implies that $\mathcal A$ is a pure density state corresponding to maximum entangled state.

This is the wording on PDF page 13. The corresponding TeX is `dflw19May17.tex`, line 878, with the equation label `maxinsepin`. The source TeX has md5 `1a948baafea109a303b169459eff9371`. See also [the literature note](../Library/Entropy/derksenfriedlandlimwang2017entanglement.md).

For $\mathbf n=(n_1,\ldots,n_d)$, the source defines $\|\mathcal T\|_1$ as the complex tensor nuclear norm, the minimum of $\sum_a\prod_j\|x_{a,j}\|_2$ over finite product decompositions $\mathcal T=\sum_a\bigotimes_j x_{a,j}$ (TeX lines 494–497), and defines $\alpha(\mathbf n,\mathbb C)=\max_{\|\mathcal T\|_2=1}\|\mathcal T\|_1$ (lines 525–526). A density tensor is the coefficient tensor of a positive semidefinite trace-one matrix, with its row and column modes kept separate (lines 680–695). Equation (6.4) is $\log_2\|\mathcal A\|_1\le 2\log_2\alpha(\mathbf n,\mathbb C)$.

Issue [#23962](https://github.com/the-omega-institute/trureturing/issues/23962) fixes the reading: for every mode count and mode-size function, every positive semidefinite trace-one complex matrix $A$ satisfying $\|\operatorname{densityTensor}(A)\|_1=\alpha(\mathbf n,\mathbb C)^2$ is $tt^*$ for some $t$ with $\|t\|_2=1$ and $\|t\|_1=\alpha(\mathbf n,\mathbb C)$. This universal implication is refuted at $d=2$, $\mathbf n=(2,4)$.

## Motivation

The source uses $\log_2\|\mathcal A\|_1$ to measure inseparability of density tensors. Lemma 6.2 gives an upper bound attained by pure densities of maximally entangled vectors. Its conjectured converse would identify all maximizing densities as pure. The equality classification therefore asks whether mixing necessarily loses this maximal value.

## Gap

The bounded literature check in #23962 is attributed to the orchestrator:

- The arXiv record has only v1; no journal version was located in that check.
- Semantic Scholar listed 24 citing records. The orchestrator reports reading the arXiv sources of ten citing works, identified there as 2608.21185, 2509.21639, 2508.07933, 2506.15609, 2011.08132, 2010.06365, 1912.07175, 1912.06854, 1803.09788 and 2309.15105, without finding discussion of this equality case.
- The preregistration records no prior repository treatment of this conjecture.

`not-found-in-searched-scope`. This does not assert that mixed maximally entangled states are new; the target is the stated tensor nuclear-norm equality conjecture.

## Route

All nuclear norms below are over $\mathbb C$, and $\|\cdot\|_2$ denotes the Euclidean norm.

1. **Projective-norm bounds.** For any finite mode type $\kappa$, any $m:\kappa\to\mathbb N$, any coefficient tensor $t$, any $r\in\mathbb N$ and factors $x_{a,j}\in\mathbb C^{m(j)}$ satisfying $t_i=\sum_{a\in\mathrm{Fin}\,r}\prod_j x_{a,j}(i_j)$, the private lemma `nuclear_le` gives $\|t\|_1\le\sum_a\prod_j\|x_{a,j}\|_2$. It uses `PiTensorProduct.projectiveSeminorm_tprod_le` on the finite family of complex Euclidean factor spaces. For the same finite mode type and sizes, any tensor $t$ and any complex-linear functional $s$ satisfying $|s(\bigotimes_j x_j)|\le\prod_j\|x_j\|_2$ for every family of factors $x_j$, the private lemma `dual_bound` gives $|s(t)|\le\|t\|_1$. It constructs a continuous multilinear map of operator norm at most one and applies `PiTensorProduct.norm_eval_le_projectiveSeminorm` to that map and the tensor represented by $t$.
2. **The pure-vector maximum at $(2,4)$.** The private lemma `row_bound` states, for every natural number $n$ and every complex coefficient tensor $t$ of shape $(2,n)$, that $\|t\|_1\le\sqrt2\|t\|_2$. It uses the two-row decomposition and Cauchy–Schwarz. Define $v_b=(e_0\otimes f_{2b}+e_1\otimes f_{2b+1})/\sqrt2$ for $b\in\{0,1\}$. The private lemma `bell_bound`, for every $x\in\mathbb C^2$ and $y\in\mathbb C^4$, bounds $|x_0y_0+x_1y_1|$ by $\|x\|_2\|y\|_2$. Thus the functional $s_0(t)=t_{0,0}+t_{1,1}$ satisfies the hypothesis of `dual_bound`; its absolute value on the unit vector $v_0$ is $\sqrt2$. The local facts `hv` and `hb` in `result` establish $\|v_0\|_2=1$ and $\|v_0\|_1=\sqrt2$. The local fact `halpha` establishes $\alpha((2,4),\mathbb C)=\sqrt2$: `row_bound` bounds the set defining the supremum, and $v_0$ supplies both its nonemptiness and attainment of that bound.
3. **The density and its upper bound.** Set $A=\tfrac12(v_0v_0^*+v_1v_1^*)$. The local facts `hpos`, `hgram` and `htrace` in `result` establish positive semidefiniteness, $v_b^*v_c=\delta_{bc}$ for all $b,c\in\mathrm{Fin}\,2$, and trace one. The local fact `hupper` gives $\|\operatorname{densityTensor}(A)\|_1\le2$ by applying `nuclear_le` to an explicit decomposition into eight product tensors, each of cost $1/4$.
4. **The matching dual certificate.** On tensors with mode sizes $(2,4,2,4)$, use $S(B)=\sum_{b,i,k=0}^1 B_{i,i+2b,k,k+2b}$. The private lemma `flag_bound` states, for every $x,z\in\mathbb C^2$ and $y,w\in\mathbb C^4$, that $|(x_0y_0+x_1y_1)(z_0w_0+z_1w_1)+(x_0y_2+x_1y_3)(z_0w_2+z_1w_3)|\le\|x\|_2\|y\|_2\|z\|_2\|w\|_2$. This is the bound on $S(x\otimes y\otimes z\otimes w)$ needed by `dual_bound`; it follows by splitting $y,w$ into two-coordinate blocks and applying Cauchy–Schwarz. The local facts `hsf` and `hsfa` establish this hypothesis for $S$ and $|S(\operatorname{densityTensor}(A))|=2$. Consequently the local fact `hn` establishes $\|\operatorname{densityTensor}(A)\|_1=2=\alpha((2,4),\mathbb C)^2$.
5. **The purity contradiction.** The private lemma `pure_idempotent` states, for any finite index type and any complex vector $t$ with $\|t\|_2=1$, that $(tt^*)^2=tt^*$. It converts the unit-norm hypothesis to $t^*t=1$ and uses the idempotency component of `D5.S3.Quantum.PureState.PureStateHandshake.pure_state_handshake`, with its matrix argument equal to zero. Applying `claim` to the density above would therefore give $A^2=A$. The local facts `hhalf` and `hnonzero` instead establish $A^2=A/2$ and $A\ne0$, contradicting idempotency.

## Falsifier

The certificate would not settle the source conjecture if it used a different norm, grouped the density modes differently, or relied on an empty or unbounded supremum set.

- The Euclidean norm is exactly Mathlib's `‖WithLp.toLp 2 t‖`.
- `nuclearNorm m t` is exactly `‖(Basis.piTensorProduct (fun j => PiLp.basisFun 2 ℂ (Fin (m j)))).equivFun.symm t‖`, the projective tensor norm in the product of the standard Euclidean bases. The density uses all four separate factors of sizes $(2,4,2,4)$; this is not the matrix trace norm of $A$.
- `densityTensor` assigns the left copy of each mode to the matrix row and the right copy to the column. `Matrix.vecMulVec t (star t)` therefore gives the source's pure density tensor $t\otimes\overline t$.
- `alpha` is a real supremum. At the counterexample's shape, `halpha` supplies the nonempty-set and upper-bound hypotheses of `csSup_le` and `le_csSup`. No general attainment theorem for arbitrary mode sizes is assumed.
- Although `claim` quantifies over all natural mode counts and sizes without positivity restrictions, the counterexample has two modes with positive sizes $2$ and $4$, within the source's setting. Its nuclear norm and $\alpha$ are positive, so equality of norms squared also gives equality in the source's logarithmic equation (6.4).

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:dce5e497b5259c05daf81f3233fd7e42e241660532ae72ac160f05eb89dc6dc3`;
- `claim`: `sha256:390c4c6d2c6e90e74c070ea1d7590bb0fdd7b1e605e7487acef247ab1d7fa668`.

## Triage

Tier 1 conjecture of a 2017 preprint, preregistered in issue #23962 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal implication `claim` is false: it is not the case that, for every $d\in\mathbb N$, $n:\mathrm{Fin}\,d\to\mathbb N$ and positive semidefinite trace-one complex matrix $A$ on the corresponding tensor coordinates, equality $\|\operatorname{densityTensor}(A)\|_1=\alpha(n)^2$ implies the existence of a vector $t$ with $\|t\|_2=1$, $\|t\|_1=\alpha(n)$ and $A=tt^*$.

**Computed, not formalized:** none.

**Argued, not formalized.**

- *Mechanism and a neighbouring family.* Put $P_b=v_bv_b^*$ for the two vectors in the route. For every $p\in[0,1]$, the density $A_p=pP_0+(1-p)P_1$ has the same maximal nuclear norm $2$. Indeed, each $P_b$ has a four-term product decomposition of total cost $2$, while the displayed functional satisfies $S(P_b)=2$ and is bounded by the product of factor norms on every product tensor. Convexity gives $\|\operatorname{densityTensor}(A_p)\|_1\le2$, and the functional gives the reverse inequality. The orthonormality of $v_0,v_1$ makes the two nonzero eigenvalues $p$ and $1-p$ when $0<p<1$, so these interior densities are mixed. Thus the norm has a flat maximizing segment: equality in the convexity bound does not force the spectral decomposition to have one summand. A purity characterization requires additional structure excluding such segments.
- *Surviving directions and scope.* At $p=0$ and $p=1$, these densities are pure and still attain the same value, consistent with the source's sufficient direction. The extra two-coordinate flag in the four-dimensional factor is essential to this construction; it does not decide the equality classification for balanced local dimensions or for arbitrary higher mode counts. Those classifications remain open here.
- *Effect on the source.* Lemma 6.2 asserts an upper bound and the sufficient direction from a maximally entangled pure vector to an equality density; neither assertion is contradicted. Its conjectured converse cannot characterize all maximizers. The source's later statements about pure three- and four-qubit maximizers, and its computational methods, are not refuted by this mixed density. No later explicit invocation of the equality conjecture is identified in the source text.

## ASSUMED-UNVERIFIED

The bounded citation search in #23962 does not establish exhaustive worldwide novelty or priority. Its Semantic Scholar count, ten citing-source readings, negative repository search and absence of a journal version are reports of the orchestrator and are not independently reproduced here. The arXiv page itself lists only v1 and supplies the DOI used above. The preregistration also attributes to its search contributor a reading of Li, Zhao, Fei, Fan and Liu, arXiv:0906.5445, reporting this state for other entanglement measures without evaluating the tensor nuclear norm; that reading is not independently reproduced here.

The correspondence between the source's finite-decomposition definition and the Mathlib projective norm is a mathematical interpretation, not a separate Lean equivalence theorem in this module. The logarithmic reformulation, the general density upper bound and pure-state sufficient direction quoted from the source, and all arguments under **Argued, not formalized** are not additional conclusions of `result`. The continuum of weights, its eigenvalue description, equality classifications in other dimensions and mode counts, and the real nuclear-norm analogue are not formalized by this settlement.
