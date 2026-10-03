---
bibkey: eno2010fusionqcaspectral
authors: Pavel Etingof; Dmitri Nikshych; Victor Ostrik
year: 2010
title: "Fusion categories and homotopy theory"
doi: null
url: https://arxiv.org/abs/0909.3140
claim: "Theorem 4.15 proves finiteness of braided tensor autoequivalence classes; the note also records separate QCA inputs and their limits."
strata_touched: []
license: citation-only
triage: anchor
---

# Categorical finiteness and spectral cut obstructions

Recorded 2026-09-27. Research owner: `docs/develop/theory/FUSION_SPIN_CHAIN_QCA_CUT_OBSTRUCTIONS.md`, SC continuation, §§21–27. This note records provenance; it is not a Lean proof, a coverage certificate or an independent review.

## Full braided-equivalence classes are finite

Pavel Etingof, Dmitri Nikshych and Victor Ostrik, *Fusion categories and homotopy theory*, Quantum Topology 1 (2010), 209–273. Source: https://arxiv.org/pdf/0909.3140 . The PDF identifies arXiv:0909.3140v2. Section 4.6 defines the group EqBr(B) as isomorphism classes of braided tensor autoequivalences. Theorem 4.15, printed p.26, states finiteness of BrPic(C), Out(C), Eq(C), EqBr(B), and Pic(B). The statement and its definitions were visually checked on the PDF page; the following proof uses the earlier ENO finiteness theorem.

This is finiteness of complete tensor-compatible isomorphism classes. It is stronger than observing that there are finitely many simple-object names. In the unitary setting, polar decomposition of a tensor natural isomorphism gives a unitary tensor natural isomorphism, as spelled out in SC §23.2.

The SC application only takes powers in this finite group. It does not construct a coherent categorical group action and does not silently assume the higher obstructions of ENO vanish.

## Actual infinite-net inputs

Corey Jones and Junhwi Lim, *An index for quantum cellular automata on fusion spin chains*, Annales Henri Poincaré 25 (2024), 4399–4422; https://arxiv.org/pdf/2309.10961v2 . Example 2.3 fixes the self-dual strongly tensor-generating object and actual window embeddings. Definition 2.5 fixes FDQC and its normality. Remark 3.10 identifies half-chain relative commutants with intervening window algebras; Proposition 4.1 supplies the translation index. Section 6 asks the joint-invariant classification question. These are published inputs, not consequences of finite arithmetic checks.

Corey Jones, *DHR bimodules of quasi-local algebras and symmetric quantum cellular automata*; https://arxiv.org/pdf/2304.00068 . The DHR-to-center identification is used for the whole product fusion category. The new finite-power argument does not depend on asserting that the individual translation DHR classes are already trivial, or on the earlier manuscript's external-product naturality proof.

## Known coverage and novelty boundary

Corey Jones, Kylan Schatz and Dominic J. Williamson, *Quantum Cellular Automata and Categorical Dualities of Spin Chains*, Communications in Mathematical Physics 407, 66 (2026); https://link.springer.com/article/10.1007/s00220-026-05571-y ; https://arxiv.org/html/2410.08884v3 . Corollary 1.4 proves completeness for finite groups with their regular representation. SC's rank-one criterion isolates regular multiples in integral fusion categories; it does not establish completeness for every integral-category regular object.

Carolyn Zhang, *Note on quantum cellular automata and strong equivalence*, https://arxiv.org/pdf/2306.03171 . Strong versus stable equivalence, additional symmetry-sensitive indices, and failures of some proposed complete invariant sets already appear in this literature. No priority is claimed for the broad idea that the ordinary index can miss symmetry information.

The new ordinary-proof chain is the faithful fusion-unit spectral criterion, the exact rank-one regular-object exception, a zero-index translation lattice surviving every finite-group invariant after finite powers, and recovery of signed shifts and layer permutations by a polarized cut table. Targeted searches do not certify global priority. Matrix spectral decomposition, moment log-convexity, Perron–Frobenius and finite-group power arguments are established tools.

## Repository reuse and checks

Read `D5/S3/Analytic/SeriesInequalities/CountableWeightedHolderInterpolation.lean` at `6cb2317a23559145bc4c9c2db4e01a84b57e02a8`. Its non-strict interpolation theorem is a prospective reusable foundation, not a proof of fusion-unit faithfulness, strictness, half-chain localization or the new subgroup classification. The source was not compiled in this pass.

The executed program `docs/reports/fusion-qca-cut-obstruction/cut_spectral_checks.py` uses exact integers and Fractions. Its repeated output matched `cut_spectral_results.json` byte-for-byte. The program tests finite algebra, including counterexamples when primitivity or fusion-unit faithfulness is omitted. It does not verify infinite operator algebras, DHR, the complete FDQC argument, Lean elaboration, CI, or independent correctness. No new Scribe binding is invented for these ordinary proofs.
