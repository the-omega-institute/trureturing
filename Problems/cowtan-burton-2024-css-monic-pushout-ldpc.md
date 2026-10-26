---
slug: cowtan-burton-2024-css-monic-pushout-ldpc
bibkey: cowtanburton2024csssurgery
doi: 10.22331/q-2024-05-14-1344
url: https://arxiv.org/abs/2301.13738v6
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/CssMonicPushoutLdpc.result
---

# Cowtan–Burton Conjecture D.1: LDPC monic CSS pushouts

## Problem

Alexander Cowtan and Simon Burton, *CSS code surgery as a universal construction*, Quantum 8 (2024), 1344, arXiv:2301.13738v6, Appendix D, Conjecture D.1:

> Let C• ←f• A• →g• D• be a basis-preserving monic span in Ch(MatF2), and let Q• be the pushout chain complex of this monic span. Further, let the monic span be a representative of a family of monic spans which are parameterised by some n ∈ ℕ, and let A•, C• and D• be the Z-type complexes of quantum LDPC codes. Then (Q•, Q•) is also LDPC. Formulating this conjecture properly requires specifying what it means for a monic span to be parameterised.

The settlement is Proved for the proposition in #19488, interpreting parameterisation as an arbitrary natural-indexed family.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Based length-two binary complexes | `BasedComplex`: bases `Fin (dim i)`, two `ZMod 2` matrices and their zero composite |
| Basis-preserving chain maps, Definition 3.4 | `basisMatrix`, `BPChainMap`, including both commutation identities |
| Monic span | `BPChainMap.Monic`: injectivity of each component matrix map |
| Basis-preserving pushout, Definition 5.1 and Lemma 5.4 | `glue`, `PBasis`, `sumD2`, `sumD1`, `pushoutD2`, `pushoutD1`; coefficients are fiber sums of a chosen representative column |
| Natural-indexed family | `claim` quantifies over arbitrary `A`, `C`, `D`, `φ`, `ψ` |
| Apex and feet are LDPC | The three `IsLDPC` hypotheses in `claim`; `weights2` and `weights1` count all four weights |
| Pushout family is LDPC | `result : claim`, with uniform bound $w_C+w_D$ |

Write $E_i=\operatorname{Fin}(C.\mathrm{dim}(i))\sqcup\operatorname{Fin}(D.\mathrm{dim}(i))$ and $q_i:E_i\to\mathrm{PBasis}(\varphi,\psi,i)$ for the quotient map. Under both monicity hypotheses, `D5.S3.Quantum.Information.CssMonicPushoutLdpc.pushoutD2_representative_independent` proves, for every $Y:\mathrm{PBasis}(\varphi,\psi,2)$, $y:E_2$ with $q_2(y)=Y$, and $X:\mathrm{PBasis}(\varphi,\psi,1)$,

$$\mathrm{pushoutD2}(\varphi,\psi)(X,Y)=\sum_{x\in E_1,\ q_1(x)=X}\mathrm{sumD2}(C,D)(x,y).$$

`D5.S3.Quantum.Information.CssMonicPushoutLdpc.pushoutD1_representative_independent` proves the analogous formula for $Y:\mathrm{PBasis}(\varphi,\psi,1)$, $y:E_1$ with $q_1(y)=Y$, and $X:\mathrm{PBasis}(\varphi,\psi,0)$:

$$\mathrm{pushoutD1}(\varphi,\psi)(X,Y)=\sum_{x\in E_0,\ q_0(x)=X}\mathrm{sumD1}(C,D)(x,y).$$

Thus the two matrices represent the induced maps $[y]\mapsto[\partial y]$, independently of the selected representative. The degree-two and degree-one formulas use `BPChainMap.comm2` and `BPChainMap.comm1`, respectively. The identity $\partial^Q_1\partial^Q_2=0$ is checked by the pinned experiment below; it is not delivered as a Lean theorem.

The categorical universal property is proved in prose here, rather than by a Lean categorical theorem. In degree $i$, take the free binary vector space on $\mathrm{PBasis}(\varphi,\psi,i)$. Its maps from the two feet send a basis vector $x$ to $[x]$ and agree on every apex basis vector. Any two linear maps from the feet agreeing on the apex assign equal values to each generating glued pair, so extend uniquely to a linear map on the quotient basis. The representative formulas above identify its differentials with $[y]\mapsto[\partial y]$. If the two maps from the feet are chain maps, that extension commutes with the differential on every quotient generator, hence everywhere by linearity. Uniqueness follows because those generators span. This identifies the construction with the basis-preserving pushout of Lemma 5.4.

## Motivation

LDPC closure supplies a uniform bound for the checks and qubit incidences of code surgery. The precise estimates distinguish the role of monicity from assumptions on the apex, homology and code distance.

## Gap

The row-support bound needs the two summands to embed into the quotient. The matching fact is an application of Mathlib's existing set-pushout injectivity theorem, not new content. The new estimate injects an output row support into the disjoint union of at most one row from each input block.

## Route

`monic_basis_injective` turns the component matrix hypothesis into injectivity of each basis function. `matching` transports Mathlib's set-pushout inclusions to `PBasis`. `quotient_column_card_le` applies `Finsupp.mapDomain_support` and finite image-cardinality bounds to bound a fiber-summed column support by the original support. `quotient_block_row_bound` injects the selected quotient row support into two input row supports. Both column bounds choose a representative of each quotient class and use the private representative-independence lemma to express its column as the quotient image of that representative column. The generic block column estimate bounds this image whether the representative belongs to the $C$ basis or the $D$ basis. Both row bounds use the quotient row-support estimate. All four private bounds feed `result`.

For input bounds $w_C,w_D$, the row estimate is at most $w_C+w_D$ and the column estimate is at most $\max(w_C,w_D)\leq w_C+w_D$. Applying these estimates to both degrees at every index proves the family bound. This derivation does not use the apex sparsity hypothesis.

## Falsifier

A span satisfying the binding monicity and LDPC hypotheses but violating an asserted weight bound would contradict `result`. The non-monic Appendix D examples illustrate why dropping monicity allows unbounded row merging; they are not counterexamples to the theorem.

## Evidence

The kernel-checked public theorem is `D5.S3.Quantum.Information.CssMonicPushoutLdpc.result`. The representative-independence lemmas and support estimates are private helpers used in its derivation. The proofs use pinned Mathlib and declarations of the same module; there are no frozen D5 prerequisites.

Historical literature completeness remains `ASSUMED-UNVERIFIED`.

Escape audit unfinished: [#19605](https://github.com/the-omega-institute/trureturing/issues/19605), target `D5.S3.Quantum.Information.CssMonicPushoutLdpc.result`. No successful four-slot registration is asserted.

### Experiment

[Published numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/aec75fa53f2a69d43549fdef025b847f54a63b6d/docs/reports/cowtan-burton-2024-monic-pushout-ldpc-conjecture-d1).
Command: `python3 /tmp/op-cb2301/check.py`, using the exact `check.py` bytes extracted from the pinned directory; exit 0. Script SHA-256: `44a0f10bac1c34fa1cb087d5abe4600f34445a22bf7bba4dd6f79920fc3d8740`.

Computed scope: 3000 random based monic spans; representative independence in 3000/3000, square-zero in 3000/3000, zero violations of either weight bound in either degree. Appendix D non-monic examples at $m=2,3,5,10$ have merged row weights $3,4,6,11=m+1$. The check reports `RESULT PASS`. These finite computations are supplementary evidence. The private representative-independence lemmas prove the representative formulas in the derivation of `result`; square-zero has only the computed evidence stated here. They establish no bounds on homology or distance.

## Triage

| Lane item | Status and evidence |
| --- | --- |
| Settlement | Proved in Lean: `result`, exactly the binding `claim` of #19488 |
| Explicit single-span column and row bounds | Proved in Lean: private `pushoutD2_col_bound`, `pushoutD1_col_bound`, `pushoutD2_row_bound`, `pushoutD1_row_bound`; columns bounded by the maximum and rows by the sum |
| No apex sparsity bound | Proved in prose by the uniform-bound derivation in Route from the kernel-checked single-span bounds; the public claim retains its literal apex hypothesis |
| Generic block and fiber-sum estimates | Kernel-checked: private `quotient_column_card_le`, `quotient_block_col_bound`, `quotient_block_row_bound`, for arbitrary finite index types, fiber maps and columns, with the stated injectivity hypotheses for rows; `quotient_column_card_le` is a consumed bind-only application of Mathlib |
| Escape witness | Proved in Lean: the row-support injection in private `quotient_block_row_bound`, consumed through both row bounds by `result`; matching is reused Mathlib content |
| Checker | Computed: the exact finite scope, script SHA-256, command and exit code in Evidence |
| Representative independence and induced quotient maps | Kernel-checked: private `pushoutD2_representative_independent` and `pushoutD1_representative_independent`, used by their respective column bounds, with their full formulas in Problem |
| Square-zero identity on the tested spans | Computed: holds in the 3000 random spans in Evidence; no general Lean theorem is claimed |
| Categorical universal property | Proved in prose: the quotient-generator factorization and uniqueness argument in Problem; no Lean categorical theorem is claimed |
| Thesis and complete literature screen | Open: `ASSUMED-UNVERIFIED`; no historical novelty claim |
| Neighbouring homology and code-distance bounds | Open: neither the support estimates nor the experiment settles these questions |
| Escape registration | Open: the missing dependent-family realization and audit evidence are described in #19605 |

### What the settlement shows

The decisive mechanism is a row-support injection, together with a column support-image inclusion. Monicity makes the quotient classes contain at most one basis element from each foot. This gives single-span estimates, then uniform family estimates without an apex sparsity bound. The support-image estimate itself does not use monicity; the column bounds use monicity when identifying the images of different representatives. The generic support lemmas apply beyond chain complexes to block matrices with fiber-sum row maps and chosen columns.

The Appendix D obstruction is unbounded merging of rows when the legs fail to be monic. The computed examples demonstrate it only at the four stated sizes; the source provides the general example. No optimality classification, homology bound or code-distance bound is claimed. The source's code-surgery constructions receive an LDPC support estimate under the binding monic-span hypotheses; their other hypotheses and quantitative conclusions are not altered.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The preregistration records source v1/v6, selected later works (arXiv:2407.09423, 2503.05003, 2505.01370 and 2510.14895), and an incompletely verified thesis attestation. No general monic-span LDPC settlement was found in that inspected scope. The independent thesis retrieval and the full citing-literature screen are incomplete. Mathematical proof of the binding support statement does not certify novelty or complete the unfinished escape audit. The categorical universal property is established by the prose derivation above, not a Lean categorical theorem.
