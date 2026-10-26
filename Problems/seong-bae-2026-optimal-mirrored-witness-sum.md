---
slug: seong-bae-2026-optimal-mirrored-witness-sum
bibkey: seongberahiesmayrchruscinskibae2026mirrored
doi: 10.1088/2058-9565/ae30a3
url: https://arxiv.org/abs/2510.06863v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.result
---

# Distinct optimal entanglement witnesses can have an optimal sum

## Problem

J. Seong, A. Bera, B. C. Hiesmayr, D. Chruściński and J. Bae, *Mirrored Entanglement Witnesses for Multipartite and High-Dimensional Quantum Systems*, arXiv:2510.06863v2, Quantum Sci. Technol. 11, 015037 (2026), ask in “Open problems”, item 2:

> Optimal EWs can be mirrored via another EW, as shown in Eq. (\ref{eq:gmeew_form}). Since optimal EWs are generally not extremal, yet, it remains unanswered whether a pair of optimal EWs can be mirrored through another optimal EWs.

This quotation is from the downloaded v2 source `mn_revision_clean.tex`, line 1749, MD5 `08daa608d307e41e61bcd9c0d9f06c31`. The generalized mirroring relation is $W+M=K$ in lines 1688–1692; the witness definition, detection sets, optimality and spanning criterion are in lines 276–281, 388–396 and 485–490. See [the literature note](../Library/QuantumContext/seongberahiesmayrchruscinskibae2026mirrored.md).

Issue [#20970](https://github.com/the-omega-institute/trureturing/issues/20970) fixes a nontrivial reading: for every natural number $d\ge3$, there are optimal witnesses $W,M$ on $\mathbb C^d\otimes\mathbb C^d$ such that $W+M$ is optimal, each detects a density matrix the other does not, and some density matrix is detected by both. This is proved.

Here a density matrix is positive semidefinite with trace one; a witness is Hermitian, block-positive on every product vector, and has negative real trace pairing with some density matrix. Optimality means that for every real $\epsilon>0$ and every nonzero positive semidefinite $P$, the operator $A-\epsilon P$ is not block-positive. Write $D_A=\{\rho:\rho\text{ is a density matrix},\ \operatorname{Re}\operatorname{tr}(A\rho)<0\}$.

## Motivation

The source’s generalized mirroring framework allows overlapping detection sets and asks about decomposing non-extremal witnesses into optimal ones (lines 1692–1696). Requiring the connecting operator $K$ itself to be optimal tests whether addition can preserve optimality while combining genuinely different detection sets. Incomparability excludes the proportional-witness example, and overlap requires a state detected in common.

## Gap

The bounded literature check is recorded in #20970:

- The v2 source retains the question at line 1749 quoted above.
- The search contributor reported that OpenAlex W4415317477 listed two citing records for one hypergraph-state work, DOI 10.2139/ssrn.6451173 and DOI 10.1016/j.optlastec.2026.115531. The full texts returned HTTP 403; only metadata was read.
- The same contributor reported that Chruściński, Bera, Bae and Hiesmayr, arXiv:2503.04158v1 (2025), addresses identity mirroring of optimal non-decomposable witnesses; no entry was found in MathDB or google-deepmind/formal-conjectures.
- The orchestrator reported that web searches for optimal witnesses mirrored through an optimal witness returned the source and its predecessors, and that the repository search found no existing settlement.

`not-found-in-searched-scope`. The reported citation, predecessor, database and web searches were not independently reproduced for this dossier.

## Route

For $d>0$ and $r\in\mathrm{Fin}\,d$, write
$A_r=|0r\rangle\langle0r|+|r0\rangle\langle r0|-|00\rangle\langle rr|-|rr\rangle\langle00|$,
the operator `wr r`. Put $q(x)=x\otimes\bar x$.

1. **Block positivity.** For $d>0$, every index $r$ and arbitrary $x,y\in\mathbb C^d$, `product_expectation` gives $\langle x\otimes y,A_r(x\otimes y)\rangle=|x_0\bar y_r-x_r\bar y_0|^2$. Under the same dimension and index conditions, `wr_hermitian` and `wr_blockPositive` give Hermiticity and block positivity.
2. **Spanning zeros.** For $d>0$, every $r$ and every $x$, `wr_zero` gives $\langle q(x),A_rq(x)\rangle=0$. For every natural $d$, including zero, `conjugate_products_span` states that the complex linear span of all $q(x)$ is the entire tensor space. Its polarization identity expresses $x\otimes\bar y$ using $q(x+y)$, $q(x+iy)$, $q(x)$ and $q(y)$.
3. **The optimality criterion.** For any natural $d$, `spanning_optimal` assumes that $A$ is a witness and that a set $S$ spans the entire complex tensor space, with every $v\in S$ a product vector satisfying $\langle v,Av\rangle=0$. For $\epsilon>0$ and positive semidefinite $P$, block positivity of $A-\epsilon P$ forces $\langle v,Pv\rangle=0$, hence $Pv=0$, on $S$. Spanning forces $P=0$, excluding every nonzero positive semidefinite subtraction.
4. **Witnesses and their sum.** For $d>0$, `omega_density` supplies the density matrix of $\Omega=d^{-1/2}\sum_i|ii\rangle$. For $r\ne0$, `omega_expectation` gives $\operatorname{tr}(A_r|\Omega\rangle\langle\Omega|)=-2/d$. Thus `wr_optimal` requires $d>0$ and $r\ne0$. For $d>0$ and nonzero $r,s$, `sum_optimal` uses the same spanning zeros and the negative pairing $-4/d$ to prove $A_r+A_s$ optimal; it does not require $r\ne s$.
5. **Different, overlapping detection sets.** For $d>0$ and $r\ne0$, `pair_density` supplies $\rho_r=|\psi_r\rangle\langle\psi_r|$, where $\psi_r=(|00\rangle+|rr\rangle)/\sqrt2$. For $d>0$, nonzero $r$ and arbitrary $s$, `pair_expectation` gives $\operatorname{tr}(A_r|\psi_s\rangle\langle\psi_s|)=-1$ if $r=s$, and zero otherwise. With $r,s$ both nonzero and distinct, `detection_separation` uses $\rho_r$, $\rho_s$ and $|\Omega\rangle\langle\Omega|$ for the two differences and the intersection. For every $d\ge3$, `result` chooses $r=1,s=2$ and takes $W=A_1$, $M=A_2$.

## Falsifier

The proof would not answer the registered question if it only supplied a block-positive sum, proportional witnesses, or unnormalized detecting states. The module’s definitions require:

- `IsWitness A`: Hermiticity, nonnegative complex expectation on every product vector, and a strictly negative real trace pairing with a positive semidefinite trace-one matrix;
- `IsOptimalWitness A`: `IsWitness A` together with failure of block positivity after every subtraction $\epsilon P$ with real $\epsilon>0$, $P\ge0$ and $P\ne0$;
- `Detects A ρ`: a positive semidefinite trace-one matrix $\rho$ with strictly negative real trace pairing;
- `claim`: all three optimality assertions, a density matrix in each detection-set difference, and a density matrix in their intersection, for every $d\ge3$.

No trace normalization is imposed on $W,M$ or $W+M$. The source’s separable-state definition and the module’s product-vector definition are connected by the finite-dimensional convex-combination interpretation of separability; that dictionary is not separately formalized here. The claim concerns generalized mirroring, without requiring $W+M$ to be a scalar identity or the witnesses to be non-decomposable.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.lean` (272 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom. The scratch import and `#print axioms` on `result` completed successfully, and the source scan found none of those constructs.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.lean.json`, statement `sha256:5418869116b6806321925b5f8249002cd8562c3d96df386565a720d79fe03782`.

Declaration statements:

- `result`: `sha256:d87811c13535c323f12621d64f3882ef63155bae91faa92a10b28338aaaaa6ca`;
- `claim`: `sha256:1c1f3254e90a04931d3734e8f017e01cd0a5e530d6c619ec385ee1f2824dc851`.

## Triage

Tier 1 explicit open problem of a 2025–2026 paper, preregistered in issue #20970 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural number $d\ge3$, there exist witnesses $W,M$ on $\mathbb C^d\otimes\mathbb C^d$ such that $W$, $M$ and $W+M$ are optimal in the positive-subtraction sense above, some density matrix is detected by $W$ but not $M$, another is detected by $M$ but not $W$, and some density matrix is detected by both.

**Argued, not formalized.**

- *Decisive mechanism and extension.* The shared spanning zeros prevent positive subtraction even when the operators are added. More generally, fix $d\ge2$ and real coefficients $a_r\ge0$, $1\le r<d$, not all zero. For $A=\sum_{r=1}^{d-1}a_rA_r$, the Hermiticity and square-expectation identities in `wr_hermitian` and `product_expectation` apply because $d>0$ and each $r$ is an index. They make $A$ Hermitian and block-positive. Each nonzero $r$ satisfies the hypotheses of `omega_expectation`, giving $\operatorname{tr}(A|\Omega\rangle\langle\Omega|)=-2\sum_ra_r/d<0$; `omega_density` applies since $d>0$. Thus $A$ is a witness. The hypotheses of `wr_zero` hold for every summand, so $q(x)$ is a zero for $A$; `conjugate_products_span` applies to this natural $d$. These facts provide every hypothesis of `spanning_optimal`: a witness, a spanning set, and zero expectation on each of its product vectors. Hence every such nonzero nonnegative combination is optimal. This weighted-sum statement is not the type of `result` and has no separate formal declaration here.
- *Non-extremality.* For $d\ge3$, the nonzero distinct indices $1,2$ satisfy the hypotheses of `pair_density` and `pair_expectation`. Pairings $(-1,0)$ and $(0,-1)$ show that $A_1,A_2$ are not proportional. Both are block-positive by `wr_blockPositive`, whose dimension hypothesis is $d>0$. Therefore their decomposition of $K$ prevents its ray from being extreme in the block-positive cone: extremality would force both summands to be proportional to $K$. Optimality and extremality impose different conditions.
- *Decomposability.* For every $d\ge2$ and $1\le r<d$, put $z_r=|0r\rangle-|r0\rangle$. Expanding $z_rz_r^\dagger$ and applying $(|ab\rangle\langle cd|)^{\Gamma_B}=|ad\rangle\langle cb|$ gives $A_r=(z_rz_r^\dagger)^{\Gamma_B}$. Thus the constructed witnesses and their sum are decomposable. For any PPT density matrix $\rho$, $\operatorname{tr}(A_r\rho)=\operatorname{tr}(z_rz_r^\dagger\rho^{\Gamma_B})=z_r^\dagger\rho^{\Gamma_B}z_r\ge0$; the sum has the same restriction. This construction cannot supply PPT detection or a family of non-decomposable witnesses.
- *Dimension and local unitaries.* At $d=2$ there is only one nonzero index, so this family supplies only one positive ray and cannot give incomparable detection sets. Necessity of $d\ge3$ for arbitrary witnesses remains open here. For $d\ge3$, simultaneously swapping levels $1$ and $2$ on both factors sends each of the four matrix units defining $A_1$ to the corresponding unit of $A_2$. The pair is locally unitarily equivalent; locally inequivalent pairs are outside this settlement.
- *Effect on the paper.* Item 2 receives an affirmative answer on the registered generalized reading. The class-II construction in “Bipartite systems: generalization” (lines 1698–1740) establishes its witness sum without assuming an answer to item 2; this settlement does not establish optimality of that particular sum. The source’s identity-mirroring proposition, $D_W\cap D_M=\emptyset$ under $W+M=\mu I$ with $\mu\ge0$ (lines 521–536), is unaffected: two negative trace pairings cannot sum to $\mu$. The present optimal $K$ has negative pairing on a density matrix, so it cannot be such a nonnegative scalar identity. Consequently the higher-dimensional identity-mirroring question in item 1 and the local-inequivalence question in item 5 are not settled by this family. No additional source conclusion depending on an affirmative answer to item 2 was identified in the checked sections.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The v2 source, its bibliographic arXiv record and the relevant source passages were read directly; the reported v1 reading, OpenAlex citation listing, inaccessible citing full texts, predecessor, MathDB, formal-conjectures, web and earlier repository searches were not independently reproduced. Metadata-only citing records cannot exclude a settlement in their full texts.

The separable-state/product-vector dictionary is not separately formalized. The weighted-sum extension, non-extremality, partial-transpose and PPT arguments, local-unitary equivalence, sharpness discussion and source-impact analysis are not asserted as additional conclusions of `result`. The existence question for arbitrary witnesses at $d=2$, non-decomposable variants, identity-mirrored variants and locally inequivalent variants remains outside this formal result.
