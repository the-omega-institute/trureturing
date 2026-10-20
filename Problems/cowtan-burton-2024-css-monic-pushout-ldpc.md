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

The settlement is Proved for the binding proposition in #19488, interpreting parameterisation as an arbitrary natural-indexed family.

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

Representative independence, the square-zero identity and the categorical universal property of the selected matrices are not Lean theorems in this module. The binding claim is a support-bound statement about the explicitly selected quotient matrices. Representative independence and square-zero have the finite experimental evidence described below; a universal formal bridge to the categorical pushout is open.

## Motivation

LDPC closure supplies a uniform bound for the checks and qubit incidences of code surgery. The precise estimates distinguish the role of monicity from assumptions on the apex, homology and code distance.

## Gap

The row-support bound needs the two summands to embed into the quotient. The matching fact is an application of Mathlib's existing set-pushout injectivity theorem, not new content. The new estimate injects an output row support into the disjoint union of at most one row from each input block.

## Route

`monic_basis_injective` turns the component matrix hypothesis into injectivity of each basis function. `matching` transports Mathlib's set-pushout inclusions to `PBasis`. `quotient_column_card_le` bounds a fiber-summed column support by the original support. `quotient_block_row_bound` injects the selected quotient row support into two input row supports. The four private `pushoutD*_row_bound` and `pushoutD*_col_bound` specializations feed `result`.

For input bounds $w_C,w_D$, the row estimate is at most $w_C+w_D$ and the column estimate is at most $\max(w_C,w_D)\leq w_C+w_D$. Applying these estimates to both degrees at every index proves the family bound. This derivation does not use the apex sparsity hypothesis.

## Falsifier

A span satisfying the binding monicity and LDPC hypotheses but violating an asserted weight bound would contradict `result`. The non-monic Appendix D examples illustrate why dropping monicity allows unbounded row merging; they are not counterexamples to the theorem.

## Evidence

The kernel-checked declaration is `D5.S3.Quantum.Information.CssMonicPushoutLdpc.result`. Its proof uses only pinned Mathlib and private declarations of the same module; there are no frozen D5 prerequisites.

The independent mirror and judgement-form assessment covers the literal public definitions and expanded result formula. Historical literature completeness remains `ASSUMED-UNVERIFIED`.

Escape audit unfinished: [#19605](https://github.com/the-omega-institute/trureturing/issues/19605), target `D5.S3.Quantum.Information.CssMonicPushoutLdpc.result`. No successful four-slot registration is asserted.

### Experiment

[Published numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/aec75fa53f2a69d43549fdef025b847f54a63b6d/docs/reports/cowtan-burton-2024-monic-pushout-ldpc-conjecture-d1).
Command: `python3 docs/reports/cowtan-burton-2024-monic-pushout-ldpc-conjecture-d1/check.py`, in that experiments checkout; exit 0. Script SHA-256: `44a0f10bac1c34fa1cb087d5abe4600f34445a22bf7bba4dd6f79920fc3d8740`.

Computed scope: 3000 random based monic spans; representative independence in 3000/3000, square-zero in 3000/3000, zero violations of either weight bound in either degree. Appendix D non-monic examples at $m=2,3,5,10$ have merged row weights $3,4,6,11=m+1$. The check reports `RESULT PASS`. These finite computations establish neither a universal formal pushout bridge nor bounds on homology or distance.

## Triage

| Lane item | Status and evidence |
| --- | --- |
| Settlement | Proved in Lean: `result`, exactly the binding `claim` of #19488 |
| Explicit single-span column and row bounds | Proved in Lean: private `pushoutD2_col_bound`, `pushoutD1_col_bound`, `pushoutD2_row_bound`, `pushoutD1_row_bound`; columns bounded by the maximum and rows by the sum |
| No apex sparsity bound | Proved in prose by the uniform-bound derivation in Route from the kernel-checked single-span bounds; the public claim retains its literal apex hypothesis |
| Generic block and fiber-sum estimates | Proved in Lean: private `quotient_column_card_le`, `quotient_block_col_bound`, `quotient_block_row_bound`, for arbitrary finite index types, fiber maps and selected columns, with the stated injectivity hypotheses for rows |
| Escape witness | Proved in Lean: the row-support injection in private `quotient_block_row_bound`, consumed through both row bounds by `result`; matching is reused Mathlib content |
| Checker | Computed: the exact finite scope, script SHA-256, command and exit code in Evidence |
| Independent proof/source fidelity and completion | Open: the supplied independent mirror assessment approves the literal binding definitions and full result formula; completion of the full source-to-categorical-pushout bridge is not established |
| Thesis and complete literature screen | Open: `ASSUMED-UNVERIFIED`; no historical novelty claim |
| Neighbouring homology and code-distance bounds | Open: neither the support estimates nor the experiment settles these questions |
| Escape registration | Open: the missing dependent-family realization and audit evidence are described in #19605 |

### What the settlement shows

The decisive mechanism is a row-support injection, together with a column support-image inclusion. Monicity makes the quotient classes contain at most one basis element from each foot. This gives single-span estimates, then uniform family estimates without an apex sparsity bound. The column estimate itself does not use monicity. The generic support lemmas apply beyond chain complexes to block matrices with fiber-sum row maps and chosen columns.

The Appendix D obstruction is unbounded merging of rows when the legs fail to be monic. The computed examples demonstrate it only at the four stated sizes; the source provides the general example. No optimality classification, homology bound or code-distance bound is claimed. The source's code-surgery constructions receive an LDPC support estimate under the binding monic-span hypotheses; their other hypotheses and quantitative conclusions are not altered.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The preregistration records source v1/v6, selected later works (arXiv:2407.09423, 2503.05003, 2505.01370 and 2510.14895), and an incompletely verified thesis attestation. No general monic-span LDPC settlement was found in that inspected scope. The independent thesis retrieval and the full citing-literature screen are incomplete. Mathematical proof of the binding support statement does not certify novelty or replace the open categorical bridge and unfinished escape audit.
