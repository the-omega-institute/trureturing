---
bibkey: griess1981monsterlocalcompletion
authors: Robert L. Griess Jr.
year: 1981
title: "A construction of F1 as automorphisms of a 196,883-dimensional algebra"
doi: 10.1073/pnas.78.2.689
claim: "Griess's algebra and its cubic form are published inputs to the Monster local-completion and cubic-response discussion."
strata_touched: []
license: citation-only
triage: anchor
---

# Monster local completion and cubic response: primary-source record

Research date: 2026-09-28. Owner: [Monster local completion and cubic response](../../docs/develop/theory/MONSTER_LOCAL_COMPLETION_AND_CUBIC_RESPONSE.md), continuing PR #10310. This records external inputs and ordinary derivations, not a Lean proof or a formalization-status claim.

## Actual construction and the hidden information

Robert L. Griess Jr., *A construction of F1 as automorphisms of a 196,883-dimensional algebra*, PNAS 78 (1981), 689–691. https://doi.org/10.1073/pnas.78.2.689 . The author's abstract explicitly describes the commutative nonassociative algebra and equivalent cubic-form realization. The short PDF was obtained; the full 1982 construction was not reverified. Its correct DOI is https://doi.org/10.1007/BF01389186 . Do not substitute the DOI of Conway's 1985 paper.

Robert L. Griess Jr. and Ching Hung Lam, *A new existence proof of the Monster by VOA theory*, https://arxiv.org/pdf/1103.1414v2 . Read the actual construction strategy, the centralizer section, and the finite Monster-type recognition route. The introduction, PDF page 2, was visually checked. The construction starts with a simple-current extension of three copies of the fixed-point sqrt(2)E8 VOA, not an assumed Monster representation. The shape 2^(1+24).Co1 and the recognition/uniqueness input retain their published attribution. The dot does not assert a split extension.

Yasuyuki Kawahigashi and Roberto Longo, *Local conformal nets arising from framed vertex operator algebras*, https://arxiv.org/pdf/math/0407263v2 . Read Theorem 3.6, Example 3.8, Lemma 5.1 and Theorem 5.4. PDF pages 15 and 20 were visually checked. This is the explicit mathematical-physics input: a holomorphic local net with only the vacuum irreducible DHR sector, while its full automorphism group is Monster. The 196883-dimensional primary module is irreducible and minimal among nontrivial complex Monster representations. No generic finite-trace spin-chain identification is inferred.

Toshiyuki Abe, Ching Hung Lam and Hiromichi Yamada, *A remark on Z_p-orbifold constructions of the Moonshine vertex operator algebra*, https://arxiv.org/html/1705.09022v4 . Section 1 identifies the original reflection orbifold and other prime orbifold presentations of the same Moonshine model. The local-extension/OPE construction is a substantive external input; the vector-space direct sum alone is insufficient.

## Selection and interaction data

Atsushi Matsuo, *Norton's Trace Formulae for the Griess Algebra of a Vertex Operator Algebra with Larger Symmetry*, Commun. Math. Phys. 224 (2001), 565–591. https://doi.org/10.1007/s00220-001-0565-3 . Actual full-text version read: https://arxiv.org/pdf/math/0007169v1 . Sections 1 and 3.1 and Corollary 4.1 were read; PDF pages 7, 13 and 16 were visually checked. Preserve the class S8 and Gram/idempotent hypotheses. For primary labels perpendicular to omega, the full Norton formulas reduce to Tr(R_u R_v)=4620(u,v) and Tr(R_u R_v R_w)=900 T(u,v,w).

The displayed v1 equations (3.2),(3.4) have an elimination polynomial whose negative roots differ from the nearby prose list. The companion program expands the polynomials exactly. The manuscript uses only the verified positive branches 1/2, 24 and 142/5, with dimensions 1, 196884 and -164081. It does not claim to have checked that printing in the final journal version.

Chongying Dong, Robert L. Griess Jr. and Ching Hung Lam, *On the uniqueness of the moonshine vertex operator algebra*, https://arxiv.org/pdf/math/0506321v1 . Theorem 1, visually checked on PDF page 1, includes the hypothesis that the weight-two algebra is the Griess algebra, in addition to central charge, weight-one and rationality/cofiniteness conditions. This hypothesis is not deleted. The historical result is not used to make a claim about the current unrestricted uniqueness literature.

Yongchang Zhu, *Modular invariance of characters of vertex operator algebras*, JAMS 9 (1996), 237–302. https://doi.org/10.1090/S0894-0347-96-00182-8 . Read the introduction from the author's uploaded full-text copy, including its statement of Theorem 5.3.2's scope; did not reverify its 66-page proof. The manuscript explicitly states the one-dimensional character representation used in its elementary low-central-charge argument.

## Defect associativity and physical consistency

Theo Johnson-Freyd, *The Moonshine Anomaly*, https://arxiv.org/html/1707.08388v3 , Theorem 1 and Section 2. The precise external result is that the Moonshine anomaly class has order 24. The correction https://link.springer.com/content/pdf/10.1007/s00220-019-03636-9.pdf was read and visually checked; it corrects the handling editor only, not the mathematical theorem. A strict automorphism action and a nontrivial defect-junction associator are compatible notions.

Ying-Hsuan Lin, *Topological modularity of Monstrous Moonshine*, https://arxiv.org/html/2207.14076v3 . Section 3 retains the order-24 anomaly and the limitation to anomaly-free gauging subgroups. The paper's partition-function constructions are not themselves a construction of the Griess multiplication.

## Current derived scope

The manuscript derives the precise cubic reconstruction/stabilizer interface, ancestry-marker centralizer and group-average mixing, an eight-setting finite-pulse estimator with real-form cancellation of first-order bias, and local stability of a finite cubic stabilizer. The resulting scalar bound is 29645*sqrt(4620)*t^2 + (43752/25)*epsilon/t^3, giving an epsilon^(2/5) upper-bound rate. It assumes explicitly declared controls and normalized complex-trace measurements. It is neither a reported hardware experiment nor a dimension-free full-tensor protocol.

Only finite exact coefficient/arithmetic checks and explicitly labelled toy permutation/cocycle models were executed. They do not instantiate actual Monster matrices, the full Griess tensor, a VOA, a conformal net or a Monster cohomology class. The general proofs remain ordinary mathematics; no new Lean/Scribe binding, independent review or global priority claim is supplied.

## Verified locator

- Published article and DOI declared above: https://doi.org/10.1073/pnas.78.2.689
- Full 1982 construction DOI cited in the scope note: https://doi.org/10.1007/BF01389186
- Griess--Lam paper: https://arxiv.org/pdf/1103.1414v2
- Kawahigashi--Longo paper: https://arxiv.org/pdf/math/0407263v2
- Abe--Lam--Yamada paper: https://arxiv.org/html/1705.09022v4
- Matsuo paper and read copy: https://doi.org/10.1007/s00220-001-0565-3 and https://arxiv.org/pdf/math/0007169v1
- Dong--Griess--Lam paper: https://arxiv.org/pdf/math/0506321v1
- Zhu paper: https://doi.org/10.1090/S0894-0347-96-00182-8
- Johnson--Freyd paper and correction: https://arxiv.org/html/1707.08388v3 and https://link.springer.com/content/pdf/10.1007/s00220-019-03636-9.pdf
- Lin paper: https://arxiv.org/html/2207.14076v3
