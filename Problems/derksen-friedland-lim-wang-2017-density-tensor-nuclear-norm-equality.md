---
slug: derksen-friedland-lim-wang-2017-density-tensor-nuclear-norm-equality
bibkey: derksenfriedlandlimwang2017entanglement
doi: 10.48550/arXiv.1705.07160
url: https://arxiv.org/abs/1705.07160v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.result
---

# A mixed density tensor attains the Derksen–Friedland–Lim–Wang nuclear-norm maximum

## Problem

H. Derksen, S. Friedland, L.-H. Lim and L. Wang, *Theoretical and computational aspects of entanglement* (2017), arXiv:1705.07160v1, §6, page 13, immediately after the proof of Lemma 6.2:

> We conjecture that equality in (6.4) implies that $\mathcal A$ is a pure density state corresponding to maximum entangled state.

The same sentence is at line 878 of the source file `dflw19May17.tex`, with the equation reference written as `\eqref {maxinsepin}`. The downloaded TeX has md5 `1a948baafea109a303b169459eff9371`.

For a complex tensor $T$ of shape $\mathbf n=(n_1,\ldots,n_d)$, the source defines its nuclear norm using finite product decompositions and Euclidean factor norms, and defines $\alpha(\mathbf n,\mathbb C)$ as the maximum nuclear norm of a Euclidean-unit tensor (TeX lines 494–497 and 525–526). A density tensor $\mathcal A$ is the $2d$-mode coefficient array of a positive semidefinite trace-one matrix on $\bigotimes_j\mathbb C^{n_j}$; a pure density tensor has the form $T\otimes\overline T$ for a unit $T$ (lines 675–695). Lemma 6.2, page 12, states:

> A density tensor $\mathcal A\in\mathbb H^{\mathbf n\times\mathbf n}_{+,1}$ satisfies inequality
> $\log_2\|\mathcal A\|_1\le2\log_2\alpha(\mathbf n,\mathbb C).$
> Equality holds if $\mathcal A=T\otimes\overline T$ and $T$ is maximum entangled.

Issue [#23962](https://github.com/the-omega-institute/trureturing/issues/23962) fixes the conjecture's reading: for every number of modes $d$, mode sizes $n$, and positive semidefinite trace-one complex matrix $A$, equality $\|\operatorname{densityTensor}(A)\|_1=\alpha(n)^2$ implies that $A=tt^*$ for some $t$ with $\|t\|_2=1$ and $\|t\|_1=\alpha(n)$. This universal assertion is refuted.

## Motivation

The paper uses $\log_2\|\mathcal A\|_1$ to measure inseparability. Its upper bound is attained by pure maximally entangled states. The conjectured converse would identify every maximizer as pure, making saturation a purity certificate. A mixed maximizer separates maximal value of this measure from purity.

## Gap

Issue #23962 records the orchestrator's bounded literature check: Semantic Scholar listed 24 citing records, and the arXiv sources of ten were inspected (2608.21185, 2509.21639, 2508.07933, 2506.15609, 2011.08132, 2010.06365, 1912.07175, 1912.06854, 1803.09788 and 2309.15105). No discussion settling the equality case of (6.4) was found in that scope.

The issue also attributes to the search seat a prior-art comparison with Li, Zhao, Fei, Fan and Liu (2012), arXiv:0906.5445: the same mixed state occurs there for other entanglement measures, without an evaluation of its tensor nuclear norm. Those citing-source readings and that comparison are not independently reproduced here. The bounded conclusion is `not-found-in-searched-scope`, with the nuclear-norm certificate distinguished from the already known phenomenon of mixed maximally entangled states in unequal local dimensions.

## Route

All vector norms below are Euclidean. For a finite mode type $\kappa$, sizes $m:\kappa\to\mathbb N$, and coefficient tensor $t:(\prod_j\mathrm{Fin}(m_j))\to\mathbb C$, `nuclearNorm m t` is Mathlib's projective tensor norm
$\|(\operatorname{Basis.piTensorProduct}(j\mapsto\operatorname{PiLp.basisFun}\ 2\ \mathbb C\ (\mathrm{Fin}(m_j)))).\operatorname{equivFun.symm}(t)\|$.
The Euclidean coefficient norm is `‖WithLp.toLp 2 t‖`, and `alpha m` is the supremum of `nuclearNorm m t` over coefficient tensors with that norm equal to one.

1. **Product and dual bounds.** For every finite $\kappa$, sizes $m$, natural $r$, and family of vectors $x_{aj}\in\mathbb C^{m_j}$, the private lemma `nuclear_le` assumes the exact coefficient decomposition $t_i=\sum_{a<r}\prod_jx_{aj}(i_j)$ and gives $\|t\|_1\le\sum_{a<r}\prod_j\|x_{aj}\|_2$. For the same finite modes and any complex-linear functional $s$, the private lemma `dual_bound` assumes $|s(\otimes_jx_j)|\le\prod_j\|x_j\|_2$ for every family of factor vectors and gives $|s(t)|\le\|t\|_1$ for every coefficient tensor $t$. These lemmas use `PiTensorProduct.projectiveSeminorm_tprod_le` and `PiTensorProduct.norm_eval_le_projectiveSeminorm`, respectively.
2. **The two-mode maximum.** For every natural $q$ and every complex coefficient tensor $t$ of shape $(2,q)$, `row_bound` gives $\|t\|_1\le\sqrt2\|t\|_2$. For every $x\in\mathbb C^2$ and $y\in\mathbb C^4$, `bell_bound` gives $|x_0y_0+x_1y_1|\le\|x\|_2\|y\|_2$. Set $n=(2,4)$ and $v_0=(|00\rangle+|11\rangle)/\sqrt2$. The functional adding coefficients $(0,0)$ and $(1,1)$ therefore satisfies the hypothesis of `dual_bound` and gives $\|v_0\|_1\ge\sqrt2$; `row_bound` gives the reverse inequality. The set defining `alpha n` is nonempty, witnessed by the unit tensor $v_0$, and is bounded above by $\sqrt2$ by `row_bound`. Since $v_0$ attains that bound, the local fact `halpha` in `result` establishes $\alpha(n)=\sqrt2$.
3. **The mixed density tensor.** Set $v_1=(|02\rangle+|13\rangle)/\sqrt2$ and $A=\tfrac12(v_0v_0^*+v_1v_1^*)$. The local fact `hgram` in `result` establishes $v_b^*v_c=\delta_{bc}$ for every $b,c\in\mathrm{Fin}(2)$. Positivity of the two outer products gives $A\succeq0$, and this Gram identity gives $\operatorname{tr}A=1$. The coefficient array `densityTensor A` has separate row and column modes, of sizes $(2,4,2,4)$. Its eight-term product decomposition has cost $8/4=2$, so `nuclear_le` gives $\|\operatorname{densityTensor}(A)\|_1\le2$.
4. **A common supporting functional.** For a coefficient array $B$ of shape $(2,4,2,4)$, put $S(B)=\sum_{b,i,k\in\{0,1\}}B_{i,i+2b,k,k+2b}$. For every $x,z\in\mathbb C^2$ and $y,w\in\mathbb C^4$, `flag_bound` states
   $|\sum_{b=0}^1(x_0y_{2b}+x_1y_{1+2b})(z_0w_{2b}+z_1w_{1+2b})|\le\|x\|_2\|y\|_2\|z\|_2\|w\|_2$.
   Thus the complex-linear $S$ satisfies the product hypothesis of `dual_bound` on these four modes. Its value on `densityTensor A` is $2$, giving the reverse bound and hence $\|\operatorname{densityTensor}(A)\|_1=2=\alpha(n)^2$.
5. **Failure of purity.** For every finite index type $\iota$ and complex vector $t:\iota\to\mathbb C$ with $\|t\|_2=1$, `pure_idempotent` states $(tt^*)^2=tt^*$. For the fixed $A$ above, the Gram identity instead gives $A^2=A/2$, while its trace one implies $A\ne0$. Hence it cannot equal $tt^*$ for any unit $t$. Applying `claim` to this $d=2$, $n=(2,4)$ and $A$ yields the contradiction proving `result : ¬ claim`.

## Falsifier

The refutation depends on retaining all four tensor modes: the nuclear norm of the density coefficient tensor is not the matrix trace norm of its $8\times8$ flattening. The definition `densityTensor` takes row coordinates from `Sum.inl` and column coordinates from `Sum.inr`, matching the source's doubled-mode construction. The norm uses complex factors with Mathlib Euclidean norms, rather than the real tensor nuclear norm or the supremum norm on coefficient functions.

The formal `claim` allows arbitrary natural mode sizes and numbers of modes. Its counterexample uses two positive sizes, $2$ and $4$, within the source's domain; it does not rely on empty or zero-dimensional cases. Although `alpha` is defined by a supremum, the proof establishes both nonemptiness and an upper bound for its defining set at $(2,4)$, together with attainment. The logarithmic equality is represented by the equality of nuclear norm with $\alpha^2$; at the witness these positive values are $2$ and $\sqrt2$.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:dce5e497b5259c05daf81f3233fd7e42e241660532ae72ac160f05eb89dc6dc3`;
- `claim`: `sha256:390c4c6d2c6e90e74c070ea1d7590bb0fdd7b1e605e7487acef247ab1d7fa668`.

## Triage

Tier 1 conjecture of a 2017 preprint, preregistered in issue #23962 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every natural $d$, size function $n:\mathrm{Fin}(d)\to\mathbb N$, and positive semidefinite trace-one complex matrix $A$ indexed by $\prod_j\mathrm{Fin}(n_j)$, equality $\|\operatorname{densityTensor}(A)\|_1=\alpha(n)^2$ implies the existence of $t$ with $\|t\|_2=1$, $\|t\|_1=\alpha(n)$ and $A=tt^*$.

**Computed, not formalized:** none.

**Argued, not formalized.**

- *Mechanism and an interval of examples.* For the two fixed vectors $v_0,v_1$ in the Route, write $P_b=v_bv_b^*$. Each $P_b$ has four product terms of cost $1/2$ each and $S(\operatorname{densityTensor}(P_b))=2$. For every $p\in[0,1]$, the density matrix $A_p=pP_0+(1-p)P_1$ therefore has a product decomposition of cost $2$, while the same complex-linear functional $S$ gives the lower bound $2$. The hypothesis needed by `dual_bound` holds for all four-factor products by `flag_bound`, with $x,z\in\mathbb C^2$ and $y,w\in\mathbb C^4$ as stated in the Route. Thus the whole segment has nuclear norm $2$. Orthogonality gives eigenvalues $p$ and $1-p$ on the span of $v_0,v_1$, so $A_p$ is mixed for $0<p<1$. The flag occupies two orthogonal two-dimensional blocks of the second subsystem. Both endpoints share a supporting functional, allowing equality under mixing; convexity does not force purity.
- *A surviving pure-state statement.* For positive mode sizes and a unit tensor $t$, the source's product rule for nuclear norms (Lemma 2.3, TeX lines 578–606), applied to $t$ and $\overline t$, gives $\|t\otimes\overline t\|_1=\|t\|_1^2$: conjugating a product decomposition preserves its cost, so the two factor norms agree. Consequently, among density tensors already assumed pure, attaining $\alpha(n)^2$ is equivalent to $\|t\|_1=\alpha(n)$, since both norms are nonnegative. The missing step in the conjecture is the inference of purity itself. Equal local dimensions, genuine multipartite systems, and the real tensor nuclear norm require separate analysis; no conclusion about these restricted questions follows from this two-mode complex example.
- *Effect on the source.* Lemma 6.2's upper bound and its sufficient pure-state equality case are compatible with the counterexample. The conjectured converse, and any identification of all maximum-inseparability density tensors as pure, must be discarded. No later explicit invocation of this equality-case conjecture was located in the v1 TeX. The pure-state extremum results, the Higuchi–Sudbery statement and the numerical algorithms are outside the refuted assertion; this settlement supplies no replacement theorem about them.

## ASSUMED-UNVERIFIED

The literature check is bounded by the citing records and ten source readings reported in #23962; those readings, the completeness of the citation listing, and the search-seat comparison with Li et al. (2012), arXiv:0906.5445, are not independently reproduced. No exhaustive worldwide novelty or priority claim is made. The source's versioned TeX, its quoted conjecture and definitions, and PDF pages 12–13 are directly checked; the arXiv abstract page supplies the e-print DOI.

The general identification of the source's attained-minimum nuclear norm with Mathlib's projective norm, the general logarithmic reformulation, the source's general upper bound and product rule, the interval $A_p$, the pure-state restriction, and the analysis of the conjecture's role in the paper are not additional formal conclusions of `result`. The norm identification uses the finite-dimensional projective-norm interpretation; no general attainment theorem is supplied by this module. Dependencies not expressed by an explicit reference to the equality conjecture remain unverified. The restricted equality questions for equal dimensions, genuine multipartite systems and real nuclear norms remain open relative to this settlement. No numerical experiment is part of this dossier.
