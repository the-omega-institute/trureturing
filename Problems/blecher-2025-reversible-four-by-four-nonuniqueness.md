---
slug: blecher-2025-reversible-four-by-four-nonuniqueness
bibkey: blecher2025commutativity
doi: 10.1016/j.exmath.2025.125742
url: https://arxiv.org/abs/2509.17673v2
triage: theorem
motivation_gids:
  - D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.result
---

# Blecher's reversible four-by-four algebra is not unique up to unitary equivalence

## Problem

D. P. Blecher, *Commutativity of operator algebras*, arXiv:2509.17673v2, Example 5.2, ends its construction of the CAR algebra $A={\rm Span}\{U,V,UV\}\subseteq M_4$ with the sentence in `3commfarx.tex`, line 684:

> We conjecture that up to unitary equivalence $A$ is the only noncommutative reversible $4 \times 4$ matrix algebra.

The preregistered formal reading takes a complex submodule $b$ of $M_4(\mathbb C)$ to be a matrix algebra when it is closed under multiplication, noncommutative when it contains a noncommuting pair, and reversible when some $m>0$ and complex-linear map $\rho:M_4(\mathbb C)\to M_m(\mathbb C)$ reverse multiplication on $b$ and preserve every block operator norm. `UnitarilyEquivalent b carAlgebra` means that some $q\in\operatorname{Matrix.unitaryGroup}(\operatorname{Fin} 4,\mathbb C)$ satisfies $x\in b$ exactly when $q^*xq\in carAlgebra$ for every $x$. Thus `claim` is the universal statement that every such $b$ is unitarily equivalent to the CAR submodule `carAlgebra`.

## Motivation

Blecher's reversible operator algebras retain their matrix norms when multiplication is reversed. The CAR construction gives a concrete noncommutative reversible algebra in $M_4$; uniqueness up to unitary conjugation would make that example a classification of the noncommutative reversible four-by-four case. A counterexample tests whether reversibility and noncommutativity determine the unitary geometry of the algebra.

## Gap

The bounded literature check recorded in preregistration issue [#24898](https://github.com/the-omega-institute/trureturing/issues/24898) found that the v2 TeX keeps the conjecture, the screened related arXiv records did not settle it, and the repository had no prior record. The issue records no citing work that resolves the four-by-four uniqueness question. The check therefore had outcome `not-found-in-searched-scope`.

## Route

1. Define
   $\operatorname{form}(t,a,b,c)$ to have possibly nonzero entries $(0,1)=tb$, $(0,2)=ta$, $(0,3)=c$, $(1,3)=a$, and $(2,3)=-b$, and let `witness` be the span of `form 2 1 0 0`, `form 2 0 1 0`, and `form 2 0 0 1`. The lemma `witness_coordinates` states, for every $x\in M_4(\mathbb C)$, that $x\in\mathrm{witness}$ exactly when $x=\operatorname{form}(2,a,b,c)$ for some $a,b,c\in\mathbb C$. The lemma `car_coordinates` gives the corresponding statement for `carAlgebra` with $t=1$.
2. For all $t,a,b,c,d,e,f\in\mathbb C$, `form_product` proves
   $\operatorname{form}(t,a,b,c)\operatorname{form}(t,d,e,f)=\operatorname{form}(t,0,0,t(bd-ae))$.
   With the coordinate lemmas, `witness_algebra` proves multiplicative closure. `witness_anticommutes` proves $xy=-(yx)$ for every $x\in\mathrm{witness}$ and $y\in\mathrm{witness}$, with the stated membership hypotheses; `witness_noncommutative` then supplies the two displayed generators and proves that their products differ.
3. `witness_reversible` takes $m=4$ and $\rho=-\mathrm{id}$. For every $x,y\in\mathrm{witness}$ it proves $\rho(yx)=\rho(x)\rho(y)$, and for every natural $n$ and every block $x:\operatorname{Fin}n\to\operatorname{Fin}n\to M_4(\mathbb C)$ whose every entry lies in `witness`, it proves equality of the norm of the entrywise $\rho$-image and the original block norm.
4. Define $\Delta(X)=2\operatorname{tr}((XX^*)^2)-\operatorname{tr}(XX^*)^2$. For every unitary $q$ and every $X$, `delta_conjugate` proves invariance of $\Delta$ under `Unitary.conjStarAlgAut \mathbb C\ _ (star q)`. `car_delta` proves $\Delta(\operatorname{form}(1,a,b,0))=0$ for all $a,b\in\mathbb C$, while `witness_delta` proves $\Delta(\operatorname{form}(2,1,0,0))=9$.
5. If $q$ is unitary and $h$ states that every image under `Unitary.conjStarAlgAut \mathbb C\ _ (star q)$ of every element of `witness` lies in `carAlgebra`, `conjugate_product_line` gives a nonzero $t\in\mathbb C$ with the image of `form 2 0 0 1` equal to $t\,\operatorname{form}(1,0,0,1)$. Under the same $q$ and the same $h$, `conjugate_complement` gives $a,b\in\mathbb C$ for which the image of `form 2 1 0 0` is `form 1 a b 0`. `witness_not_equivalent` combines that conclusion with `delta_conjugate`, `car_delta`, and `witness_delta` to rule out `UnitarilyEquivalent witness carAlgebra`. Applying `claim` to `witness`, `witness_algebra`, `witness_noncommutative`, and `witness_reversible` yields `result : ¬ claim`.

## Falsifier

The settlement would miss the source question if the formal definitions changed the quantifiers or the equivalence relation. Here `IsReversible` quantifies over every block size and every block whose entries lie in the submodule, and `UnitarilyEquivalent` uses the membership biconditional for the conjugation $x\mapsto q^*xq$; these are the definitions used by `claim`. The counterexample is therefore a falsifier of the compiled formal reading. It does not assert a classification up to similarity, a classification up to complete isometry, or a statement in any other dimension.

## Evidence

The canonical source is `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.lean`.
- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.lean.json`.

Declaration statements:
- `result`: `sha256:b3d3a2ff82fa52587975856b70f0c72a7a680ff83f66ad890b3f9cdf145b1979`;
- `claim`: `sha256:7a2e8bfaef8b515ff378d3eaf5c63a113acee6c834e494be4f22628e43e7b10b`.

## Triage

Tier 1 conjecture of a 2025 paper, preregistered in issue #24898 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** `result` has type `¬ claim`. Unfolding `claim`, it proves that not every multiplicatively closed, noncommutative, reversible complex submodule of $M_4(\mathbb C)$ is unitarily equivalent to `carAlgebra`. The proof's witness is the span of $2e_{13}+e_{24}$, $2e_{12}-e_{34}$, and $e_{14}$ in one-based matrix-unit notation; its products, anticommutation, reversibility, and separation from `carAlgebra` are established by the named lemmas in the route.

**Computed, not formalized.** None.

**Argued, not formalized.**

- *Mechanism.* The weighted coefficient $2$ preserves the alternating product formula, so the span remains anticommuting and the map $\rho=-\mathrm{id}$ reverses multiplication while preserving all matrix norms. The unitary invariant $\Delta$ vanishes on the orthogonal complement of the product line inside `carAlgebra` but takes value $9$ on the weighted generator, so unitary conjugation cannot identify the two submodules. The coordinate and trace calculations are formalized in the proof of `result`; the broader geometric interpretation is stated here as explanation.
- *Further weighted examples.* The preregistration orchestrator argues that varying the nonzero coefficient in place of $2$ produces a continuum of pairwise non-equivalent examples. That family and its pairwise separation are not formalized here.
- *Scope and repair.* The refutation shows that reversibility, complete norm preservation, and noncommutativity alone do not force the CAR unitary class. Which additional hypotheses characterize the CAR class is open here; no such repair is a theorem of `result`.
- *Effect on the source.* The CAR example's own noncommutativity and reversibility remain valid. The corollary immediately after Example 5.2, which the source derives from that example and Proposition `wiff`, does not use the uniqueness conjecture. No later source statement depending on the uniqueness conjecture was identified in the checked TeX; the source's higher-dimensional examples and questions remain outside this settlement. The implication from the preregistered finite-matrix reversibility condition to the source's abstract operator-algebra notion is the formal-reading bridge and is not a separate Lean declaration.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources and related records described in issue #24898 and does not establish exhaustive worldwide novelty or priority. The source's abstract-to-formal implication, the continuum of weighted examples, the complete-isometry comparison between the CAR and weighted algebras, any repaired uniqueness hypothesis, and all classifications in other dimensions are not formalized here. The computed and argued statements above are not additional Lean declarations; source claims outside the quoted and checked passages remain assumed-unverified.
