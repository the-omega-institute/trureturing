---
slug: op-sy2609oct
bibkey: steiningeryurkevich2026octahedron
doi: 10.48550/arXiv.2609.10788
url: https://arxiv.org/abs/2609.10788v1
triage: theorem
motivation_gids:
  - D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.result
---

# The octahedron diameter-plus-square scalar conjecture is refuted

## Problem

Jakob Steininger and Sergey Yurkevich, *The Nieuwland number of the Octahedron*, arXiv:2609.10788v1, section 3, printed page 8, propose the scalar $\Phi(P)=D(P)+(23/10)s(P)$, where $D$ is convex-hull diameter and $s$ is the smallest enclosing-square side. Their unnumbered conjecture is
$$
\sup_\pi\Phi(\pi O)\leq \frac{3\sqrt2}{4}\inf_\pi\Phi(\pi O),
\qquad O=\operatorname{conv}\{\pm e_1,\pm e_2,\pm e_3\}.
$$
The projection range consists of every real $2\times3$ matrix $M$ with $MM^{\mathsf T}=I_2$. The source is cited in [the Library note](../Library/FiniteGeometry/steiningeryurkevich2026octahedron.md); [issue #27498](https://github.com/the-omega-institute/trureturing/issues/27498) identifies the external question and its literature screen.

### Statement echo

| Source clause | Formal counterpart and boundary |
| --- | --- |
| Six signed Cartesian vertices | `shadow` uses the existing Euclidean `SymmetricBellPolytopeNotCrossPolytope.crossPolytope 3`; filling the vertices preserves their hull diameter and square containment. |
| Every orthogonal projection | `IsProjection M` is exactly $MM^{\mathsf T}=I_2$; `projectionValues` includes every such real matrix. |
| Convex-hull diameter | `diameter P` applies `Metric.diam` to the real convex hull of $P$. |
| Smallest square into which $P$ fits | `enclosingSquareLengths` quantifies over all planar special-orthogonal rotations and all Euclidean translations; `squareSide` is its infimum. Weak enclosures and strict enclosures have the same infimum by arbitrary positive enlargement. |
| Fixed coefficient $23/10$ | `octahedralScalar` uses precisely $D+(23/10)s$. |
| Supremum bounded by $(3\sqrt2/4)$ times infimum | The closed proposition `claim` is the literal real supremum/infimum inequality; `result` has type `¬ claim`. |

No extra geometric hypothesis restricts the claim. Nonnegative admissible lengths express side length; the scalar-value and enclosure sets used by the proof are nonempty and bounded in the required directions, so no empty or unbounded totalization supplies the refutation.

## Motivation

The scalar certificate would give another upper bound for the octahedron's Nieuwland number. An exact obstruction distinguishes this auxiliary scalar conjecture from the source's separate Nieuwland-number theorem and the polar-duality theorem of Satheeskumar–Benoit, arXiv:2608.14912v1, Theorem 14. The conclusion refutes only the displayed scalar certificate.

## Gap

The literature screen on #27498 found no settlement of this exact inequality in the searched scope. It covers the primary source, OpenAlex, Crossref, available arXiv searches, MathOverflow, Zenodo and readable third-party metadata. Its unavailable Semantic Scholar responses, unread thesis, unlicensed Lean sources, search-engine challenges and stale Machina snapshot prevent an exhaustive literature conclusion. Completeness is **ASSUMED-UNVERIFIED**.

## Route

Write $q=3\sqrt2/4$. Two orthonormal-row projections have matrices
$$
H=\begin{pmatrix}\sqrt2/2&-\sqrt2/2&0\\\sqrt6/6&\sqrt6/6&-\sqrt6/3\end{pmatrix},
\qquad
I=\begin{pmatrix}-1/3&2/3&2/3\\2/3&-1/3&2/3\end{pmatrix}.
$$
The private theorems `H_projection` and `I_projection` verify their projection equations. `centered_vertex_enclosure` uses antipodal vertices to eliminate arbitrary translations. For a planar rotation with entries $a,b$, put $p=|a|$, $r=|b|$; then $p^2+r^2=1$. `sorted_sharp_strip_lower` and `sharp_unit_strip_lower` combine the column-strip inequalities to give the orientation-uniform bound $s(HO)\geq1+\sqrt3/3$. `H_square_exact` supplies an attaining rotation. The corresponding private exact-value theorems for $I$ give $s(IO)=4/3$.

The private `scalar_gap` proves
$$
\Phi(HO)-q\Phi(IO)>9/1250>0.
$$
`projection_scalar_bounds` proves $0\leq\Phi(MO)\leq9$ for every admissible projection. `projection_values_bounds` supplies both finite real bounds, and `result` compares the $H$ and $I$ members with the supremum and infimum to contradict `claim`.

## Falsifier

A failure to cover every rotation or translation, a sup-norm interpretation of Euclidean distances, altered source coefficients, or empty/unbounded extrema would invalidate this encoding. The definitions retain those domains and constants. The private sharp-square and boundedness theorems discharge the continuous-orientation and finite-extrema obligations; the exact experiment supplies independent numerical and symbolic comparisons, not the Lean proof.

## Evidence

Canonical Lean source: `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.lean`.

Blueprint: `Blueprint/D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.scribe.cs` and its emitted Markdown.

Frozen state: `Golden/Frozen/state/D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.lean.json`.

The settling module has generality **I**, utility **certified-instance** with `basis=refutes`, and admission basis **open-problem-resolution (#27498; Refuted)**. The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). All other theorem declarations are private proof helpers; no owner declaration is published.

### Exact experiment

The independent checker is in [the experiments directory at commit ae622f18ab6637289c7036795a18ba5749b5d749](https://github.com/the-omega-institute/trureturing-experiments/tree/ae622f18ab6637289c7036795a18ba5749b5d749/docs/reports/sy2609oct-octahedron-square-obstruction). Script: `docs/reports/sy2609oct-octahedron-square-obstruction/check.py`; SHA-256: `55fd072af0ec65285f6c34439943de3d5ef450800dfd723b6be5394c8f3f16ff`.

Command: `python3 /Users/auric/.op-scratch/op/sy2609oct/stageb/check.py`, with that exact committed script; Python 3.14.8, SymPy 1.14.0; exit **0**, final result **ALL_CHECKS_OK**. Its tested scope is the four explicit shadows $H,I,S,Q$, the source's two displayed projections, their exact orientation-candidate reductions, the two coefficient factorizations and the rational perturbation budget. The exact orientation-candidate counts are respectively 13, 11, 3 and 15 for $H,I,S,Q$. This is a finite exact reduction over orientation breakpoints, not angular sampling.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Exact $H$ and $I$ diameter and square side, with every rotation and translation included | **Proved, kernel-checked:** private `H_diameter_exact`, `H_square_exact`, `I_diameter_exact`, `I_square_exact` give $(D,s)(HO)=(2\sqrt6/3,1+\sqrt3/3)$ and $(D,s)(IO)=(4\sqrt2/3,4/3)$. |
| The hexagonal square side defeats weight $23/10$ | **Proved, kernel-checked:** private `scalar_gap` gives $\Phi(HO)-q\Phi(IO)>9/1250$; public `result` refutes the source inequality. |
| Uniform scalar bounds and valid extrema | **Proved, kernel-checked:** private `projection_scalar_bounds` gives $0\leq\Phi\leq9$; `projection_values_bounds` gives finite real lower and upper bounds; `result` includes the $H,I$ members. |
| Relationship to the source's other results | **Computed comparison; evidence kind: literature reading** of arXiv:2609.10788v1 section 3 and its Theorem 1, and arXiv:2608.14912v1 Theorem 14. The scalar conjecture, Nieuwland-number theorem and polar-duality theorem are separate statements. This refutation negates no conclusion of the latter two theorems; this comparison is not a new Lean theorem. |
| Extra checker obligations | **Computed:** the exact experiment above verifies $S,Q$, both coefficient factorizations and the rational perturbation budget, with exit 0 and the stated script hash. These are not additional Lean theorems. |
| Coefficient obstruction pairs | **Computed:** the checker gives $(D,s)(SO)=(2,\sqrt2)$ and $(D,s)(QO)=(\sqrt3,\sqrt2)$ and the factorizations below. The conclusions for the resulting coefficient intervals are algebraic consequences of these exact values, outside this module's Lean statements. |
| Coefficients in $[c_-,c_+]$ | **Open:** whether any such coefficient makes the scalar certificate valid is not settled. |
| A neighbourhood of counterexamples | **Open in Lean:** the Hausdorff/operator-norm continuity bridge is not formalized; the checker verifies only the rational budget at radius $1/1000$. |

For the coefficient comparison, let $\Phi_c=D+cs$ and
$$
c_- = \frac{4\sqrt2/3-\sqrt3}{\sqrt2-4/3},
\qquad
c_+ = \frac{2-2\sqrt6/3}{1+\sqrt3/3-\sqrt2}.
$$
The checker verifies positive denominators, $23/10>c_+$ and the exact factorization signs: $S,Q$ obstruct $0\leq c<c_-$; $H,I$ obstruct $c>c_+$. These extensions are computed algebraic consequences, not uniform Lean theorems. The checked rational budget is $9/1250-33/5000=3/5000$; obtaining the error term $33/5000$ from nearby projections requires the unformalized continuity bridge.

The failure mechanism is the large rotation-optimized enclosing square of the regular hexagonal shadow. Exact square sides, the finite extrema bounds and the source's independent Nieuwland-number conclusion survive. No replacement coefficient or classification of all counterexamples is asserted.

## ASSUMED-UNVERIFIED

- Literature completeness and exhaustive owner discovery: searches are bounded and the unavailable readings on #27498 remain unavailable.
- The geometric continuity bridge and the validity question for $c\in[c_-,c_+]$ remain open as described in Triage.
- The exact experiment is evidence only for its stated explicit instances, factorizations and rational budget; it is not a Lean proof of the extensions.
