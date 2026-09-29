---
bibkey: carnahan2016mixeddefectselection
authors: Scott Carnahan; Masahiko Miyamoto
year: 2016
title: "Regularity of fixed-point vertex operator subalgebras"
doi: null
url: https://arxiv.org/abs/1603.05645
claim: "Fixed-point regularity and mixed trace covariance up to scalar are published inputs; exact common trace normalization remains an explicit extra hypothesis."
strata_touched: []
license: citation-only
triage: anchor
---

# Monster selection from mixed involution defects

Recorded 2026-09-28. Theory owner: `docs/develop/theory/MONSTER_LOCAL_COMPLETION_AND_CUBIC_RESPONSE.md`, new sections 12–19. This is a provenance and scope note, not a Lean theorem or an independent review.

## What the new proof actually assumes

The rank-thirteen result uses a unitary strongly rational holomorphic CFT-type VOA, c=24, V_1=0, an actual elementary abelian two-group action, and strictly positive type-2{0} twisted modules for every nonidentity element.

The rank-four result has the additional **common torus-trace realization** of Definition 14.1: honest weight-preserving centralizer actions on all actual twisted modules, diagonal action exp(2*pi*i*L_0), and one simultaneous normalization with exact S and T trace covariance. A collection of separately rephased commuting-pair functions does not satisfy this premise. Neither existence of an automorphism nor a numerical character table supplies it.

Proposition 14.2 states a concrete sufficient interface through the actual fixed-point characters with untwisted-double S/T matrices. The finite Fourier calculation is proved in the manuscript. A full general VOA theorem assembling that interface from cyclic type data is not claimed in this pass. The proved cyclic detection of H^3(F_2^r,U(1)) does not, by itself, construct that analytic realization.

## Published inputs checked

1. C. Dong and G. Mason, *Holomorphic Vertex Operator Algebras of Small Central Charges*, arXiv:math/0203005. https://arxiv.org/pdf/math/0203005 . Lemma 2.1 fixes the character J when c=24 and V_1=0. Theorem 3(b) identifies the Leech lattice VOA from a twenty-four-dimensional abelian weight-one algebra. The theorem and proof were read; this source does not prove general Moonshine uniqueness from V_1=0.

2. J. van Ekeren, S. Möller and N. R. Scheithauer, *Dimension Formulae in Genus Zero and Uniqueness of Vertex Operator Algebras*, IMRN 2020, 2145–2204; arXiv:1704.00478v3. https://arxiv.org/pdf/1704.00478 . Section 3 supplies normalized cyclic type-zero orbifold data and inverse orbifolds. Section 4.1 supplies the eta Hauptmodul. Its n=2 formula has Montague antecedents. The manuscript separately proves the specialized two-cusp calculation.

3. M. P. Tuite, *On the Relationship between Monstrous Moonshine and the Uniqueness of the Moonshine Module*, arXiv:hep-th/9305057. https://arxiv.org/pdf/hep-th/9305057 . Section 3.6 is the historical Montague/Tuite provenance for the one-defect inverse-orbifold identification. FLM's actual field construction and Monster automorphism theorem remain external inputs, as in the existing owner.

4. A. Kirillov Jr., *Modular categories and orbifold models*, Commun. Math. Phys. 229 (2002), 309–335; arXiv:math/0104242. https://arxiv.org/pdf/math/0104242 . The introduction's assumptions, Section 5, Lemma 5.3 and Theorem 5.12 concern actual group actions and double-category reconstruction in the trivial-obstruction case. They are not cited as a substitute for checking all analytic character normalizations of an arbitrary candidate VOA.

5. S. Carnahan and M. Miyamoto, *Regularity of fixed-point vertex operator subalgebras*, arXiv:1603.05645v4. https://arxiv.org/pdf/1603.05645 . Corollary 5.25 proves fixed-point regularity for finite solvable groups in the stated class. Theorem 6.2 proves mixed trace covariance **up to a nonzero scalar**. This is not silently strengthened to the exact common covariance assumed in Definition 14.1. Remark 6.4 explicitly separates the remaining constants and the established cyclic case.

6. M. R. Gaberdiel, D. Persson, H. Ronellenfitsch and R. Volpato, *Generalised Mathieu Moonshine*, arXiv:1211.7074v3. https://arxiv.org/pdf/1211.7074 . Section 3.1, equations (39)–(40), discusses general holomorphic orbifolds before its Mathieu ansatz. The double-star footnote below equation (40), printed page 18, retains a general proof limitation. It is not a numbered footnote 18. Later conjectural Mathieu elliptic genera are not premises of the new argument.

7. T. Johnson-Freyd, *The Moonshine Anomaly*, arXiv:1707.08388v3. https://arxiv.org/pdf/1707.08388 . Section 2.2 supplies the precise conformal-net anomaly setting and explains VOA/net scope. The Monster anomaly's order 24, already cited in the owner, does not imply that every subgroup or every candidate VOA automatically has the chosen trivialized torus realization.

8. J. S. Milne, *Modular Functions and Modular Forms*, v1.31 (2017). https://www.jmilne.org/math/CourseNotes/MF.pdf . Section 2 supplies compact modular-curve and cusp background. The standard level-two lambda/theta identities are explicitly stated in equation (MD.15); they are not represented as newly discovered identities. The three-cusp constant-term elimination and resulting reciprocal sign constraint are supplied in full.

9. S. Carpi and G. Codogni, *Vertex operator algebras, partition functions and Teichmüller modular forms*, arXiv:2605.26972v1. https://arxiv.org/html/2605.26972v1 . Its discussion keeps general FLM uniqueness distinct from a conditional selector with additional defect data. No higher-genus theorem from this paper is used to close our remaining assumptions.

## New synthesis and exact scope

The all-energy identity J-F_A=4096*(47/t+4096/t^2) shows why more single-insertion coefficients do not resolve the rank-twelve branch: an abstract graded representation realizes them in every degree. No VOA is thereby constructed.

Under the common realization, the three cusps of X(2) force the mixed trace to a one-dimensional line and force reciprocal ground-state signs to multiply to -1. Two disjoint binary planes produce nine such pairs. Honest character multiplication requires their total product to be +1, while reciprocity requires -1. This rules out an all-A rank-four subgroup and selects a B defect; published inverse-orbifold rigidity then identifies Moonshine.

Every four-subspace must meet the B set, giving |B|>=2^(r-3)-1. The purely finite-geometric bound is sharp for a codimension-three subspace, but that example generally fails the additional VOA character constraints. Actual VOA attainment is not claimed. Rank three has exactly eight solutions of the finite ground-sign equations, with no claim that they extend to a VOA.

The focused literature search has not established global priority for this combination. Modular functions, group cohomology, inverse orbifolds, finite character theory and blocking-set arguments have mature antecedents; these individual tools are not counted as inventions.

## Executed diagnostics and limits

`docs/reports/monster-twisted-pair-selection/twisted_pair_checks.py` uses only integer and Fraction arithmetic. It was run and rerun with byte-identical JSON. It verifies truncated character/theta identities through the stated degree, finite sign systems, the explicit nine-equation dependency, cyclic restrictions and cocycle equations, and low-dimensional blocking examples. Those overlapping finite checks are not a count of independent theorems.

Checker Git blob: `c9cef300312b370be0751bc4312060181d0ac629`.
Result Git blob: `4e2270c3ce81230d0fa7d074a16c11b5b06ca66b`.

No full VOA, conformal net, Monster representation, general analytic character realization, Lean proof, independent review or physical experiment was instantiated. Earlier sources and checks retain their original verification scopes.
