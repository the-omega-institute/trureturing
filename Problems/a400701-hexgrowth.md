---
slug: a400701-hexgrowth
bibkey: shannon2024markey2026hexgrowth
doi: null
url: https://oeis.org/A400701
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/Percolation/MarkeyFiveSiteGrowthDifference.result
---

# Markey five-site triangular growth difference

## Problem

Aidan Markey's OEIS A400701 revision 30 FORMULA conjecture asks whether five-site triangular growth exceeds the fixed-radius circle vertex count by $4n+7$ for every $n>1$. This is the sole resolution claim owned by this dossier, preregistered as [#21459](https://github.com/the-omega-institute/trureturing/issues/21459). Shannon's supporting vertex-count formulas are OEIS A374338 revision 15, independently settled under [#21460](https://github.com/the-omega-institute/trureturing/issues/21460) in `Problems/a374338-circle-vertices.md`. Neither OEIS source has a DOI or arXiv identifier.

For any distinct Euclidean starting points $a,b$, let $v(n)$ count all retained vertices after $n$ simultaneous iterations. The circle radius is always $\operatorname{dist}(a,b)$. The supporting Shannon formulas are

$$
\begin{aligned}
v(3k+1)&=(3(3k+1)^2+5(3k+1)+4)/3 &&(k\ge0),\\
v(3k)&=(3(3k)^2+5(3k))/3 &&(k\ge1),\\
v(3k-1)&=(3(3k-1)^2+5(3k-1)+2)/3 &&(k\ge1).
\end{aligned}
$$

These clauses cover exactly $n\ge1$. They make no assertion about the source's offset-zero value. The illustration labels eight total vertices at iteration 2; retained vertices, rather than eight additional vertices, are counted.

For the five consecutive axial sites $(0,0),\ldots,(4,0)$, let $a(n)$ be the count after $n$ simultaneous updates adding every site with at least two occupied neighbors in the six-direction triangular lattice. Markey's OEIS A400701 conjecture is

$$a(n)=v(n)+4n+7\qquad(n>1).$$

Both claims use the same natural iteration index. The finite window in `MarkeyA400701.latticeCount` has a spare boundary layer; `WindowTransport.finite_state` proves that its updates agree with the unrestricted process through the terminal horizon.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| arbitrary distinct initial Euclidean vertices | `ShannonA374338.claim` quantifies over `EuclideanSpace ℝ (Fin 2)` and assumes their inequality |
| unchanged radius | both sphere equations in `ShannonA374338.vertices` use the initial distance |
| all previously constructed vertices persist | the successor case of `vertices` takes the union with the preceding set |
| two distinct old circle centers | the existential centers are members of the preceding set and are unequal |
| total vertex count | `ShannonA374338.vertexCount` uses set cardinality |
| $n=3k+1$, $k\ge0$ | the first conjunct of `claim`, with natural $k$ |
| $n=3k$, $k\ge1$ | the second conjunct of `claim` |
| $n=3k-1$, $k\ge1$ | the third conjunct of `claim` |
| all three formulas | `ShannonA374338.result` proves the complete conjunction |
| five consecutive collinear sites, six unit directions, simultaneous threshold-two update | the shared `MarkeyA400701.seed`, `directions` and `latticeCount`, with `WindowTransport.finite_state` proving unrestricted-update agreement |
| $a(n)=v(n)+4n+7$ for every $n>1$ and every distinct initial pair | `MarkeyFiveSiteGrowthDifference.MarkeyA400701.claim` and `result` |

Natural-number division is the integer quotient. The named auxiliary polygons and coordinate maps are proof objects; they add no hypotheses to the source claim. The module has generality G and utility none.

## Motivation

The Euclidean process admits an exact description on the axial integer lattice. The shared module `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth` supplies the literal circle-to-lattice correspondence and exact two-site and five-site hexagons. The Shannon module supplies the symbolic residue-class count. Markey’s settling module proves the finite-window transport, identifies the unrestricted five-site shape and applies the symbolic width-three count difference.

## Gap

Finite numerical agreement alone does not prove an assertion for all iteration indices or all distinct Euclidean starting pairs. The proof requires the full geometric intersection classification, exact simultaneous-update induction and symbolic polygon count. The finite checker remains separate evidence.

## Route

In axial coordinates $(x,y)$ the quadratic form is $x^2+xy+y^2$. Two radius-one circles at distinct integer lattice centers can intersect only at lattice points whose displacements from both centers are among the six unit directions. A similarity transports this statement to arbitrary distinct starting points. Induction identifies every Euclidean circle stage with the embedded two-site retained growth stage.

For seed lengths $m=2,5$ and every $n\ge2$, the occupied set is

$$
1-n\le2x+y\le2m-3+n,\qquad
-n\le x-y\le m-1+n,\qquad
-n\le x+2y\le m-1+n.
$$

The coordinates $V=x-y+n$, $W=x+2y+n$ have $V\equiv W\pmod3$. Counting a congruence-filtered square minus two equal corners gives the three residue polynomials. The first iteration has four points and is handled separately. The inverse-coordinate map uses the existing `CubicThetaLattice.normThird` followed by translation; the forward coordinate map uses `CubicThetaLattice.normTripling` followed by translation.

## Falsifier

A distinct starting pair and an iteration $n>1$ violating $a(n)=v(n)+4n+7$ would contradict the proved Markey claim. A circle intersection outside the embedded lattice, an incorrect hexagon update for either nominated seed, or a residue-count mismatch would invalidate a corresponding bridge. Arbitrary seed lengths are outside the claim: the six-site step-2 comparison below distinguishes that extension from the proved two-seed statement.

## Evidence

The resolution node owned by this dossier is `D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.MarkeyA400701.result` for Markey [#21459](https://github.com/the-omega-institute/trureturing/issues/21459). It proves the complete literal family claim and carries a typed Proved resolution claim in its Scribe. The supporting Shannon result `D5.S3.Geometry.ShannonFixedRadiusCircleVertices.ShannonA374338.result` resolves [#21460](https://github.com/the-omega-institute/trureturing/issues/21460) and belongs to `Problems/a374338-circle-vertices.md`.

The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}. No new axiom or sorry is used.

### Finite computation

The published [experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/604fd09490d8ed3d1f66d03c2ac5c06b033c81c3/docs/reports/a400701-hexgrowth) contains `check.py`, SHA-256 `7751e963e186b3c64fa80307e6324d3a3bfb6603d72c4cb6e210c58254fe0995`. Command: `git -C /Users/auric/trureturing-experiments show 604fd09490d8ed3d1f66d03c2ac5c06b033c81c3:docs/reports/a400701-hexgrowth/check.py | python3 -`; exit 0, final marker ALL_CHECKS_OK. The exact tested scopes are 24 independent native-update equalities through step 12, both nominated shapes for steps 2 through 100, 99 five-site difference checks, 100 Shannon formula checks, 18 circle displacements and eight complete circle iterations. These finite readings do not establish the unbounded theorem.

The additional seed-length computation uses `docs/reports/a400701-hexgrowth/scope.py` in the experiments checkout, SHA-256 `2fece7936b5c7c7fa4337df51e9717fe4b2a750f1288df5a37ead07ed3f9572f`. Command: `python3 /Users/auric/trureturing-experiments/docs/reports/a400701-hexgrowth/scope.py`; exit 0, marker SCOPE_CHECKS_OK. It uses the published checker's native update and enumerates all six inequalities without restricting the vertical coordinate to the reachable step-2 strip. Its tested scope is exactly step 2 and seed lengths 2 through 6. The script is local experimental material; its publication at an immutable experiments revision is unverified.

### Escape audit

The escape audit is unfinished under [#22020](https://github.com/the-omega-institute/trureturing/issues/22020). The audit covers all new public theorems and the published coordinate maps `CubicThetaLattice.normTripling` and `CubicThetaLattice.normThird`. No retained Reg registration or declared_validated status is claimed. The missing evidence is a faithful source-family realization and reconstruction bridge, whole-family interventions and sensitivity, and actual observational dependence for the full original telescopes.

## Triage

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| common-row decomposition into three extra points per row and two new rows of length $r+1$, $r=(2n+1)\bmod3$ | open | the total difference is kernel-checked by `HexShapeCounts.count_difference`; the proposed row-by-row interpretation is not a separately proved statement here |
| supplied checker ends ALL_CHECKS_OK | computed | `check.py` command and SHA-256 above, exit 0; finite scopes only |
| six-site step-2 growth has 28 points while the literal hexagon has 30 | computed | `scope.py` command and SHA-256 above, exit 0; extra points $(1,3)$ and $(4,-3)$ |
| step-2 literal bases agree for seed lengths 2,3,4,5 | computed | same scope computation, exit 0; cardinalities 8,13,18,23 and exact set equality; no all-index extension for 3 or 4 |
| period-three corrections arise from $V\equiv W\pmod3$ | proved | proved in prose: the transformed integer coordinates satisfy $W-V=3y$; the congruence-filtered square splits into the three possible residues, and `HexCounts.polygon_zero`, `polygon_one`, `polygon_two` give their counts |
| boundary indices | computed | `check.py` checks $n=1$: the five-site and circle counts are 13 and 4, whose difference 9 is not $4+7$; the Markey claim requires $n>1$, and Shannon handles $n=1$ directly and excludes $n=0$ |
| source consequences | open | the vertex-count conjectures are settled; independent region and edge formulas need arrangement arguments and are not settled here; no source theorem depending on the Markey relation was identified in the preregistration literature reading |
| region counts, edge counts, arbitrary seed lengths, generating functions | open | outside the assertions proved here |
| exact expanding hexagons for both seed lengths 2 and 5, all $n\ge2$ | proved | kernel-checked `TriangularTwoNeighborGrowth.AxialGrowth.exact_shape` |
| every common point of two fixed-radius circles at distinct embedded centers is a unit-adjacent embedded lattice point | proved | kernel-checked `TriangularTwoNeighborGrowth.CircleGrowth.intersection_lattice`, for every distinct Euclidean starting pair |
| clipped-square hexagon update for every integer $A\ge3$, $L\ge A+2$ | proved | kernel-checked private `TriangularTwoNeighborGrowth.HexGrowth.hex_update`, consumed by `AxialGrowth.shape_step` |
| two axial unit-circle equations force the six relative unit directions | proved | kernel-checked private `TriangularTwoNeighborGrowth.HexCircleArithmetic.integer_center_intersection`; the Euclidean bridge is the separately named declaration above |
| symbolic residue-class polygon counts and width-three count difference | proved | kernel-checked `ShannonFixedRadiusCircleVertices.HexCounts.polygon_zero`, `polygon_one`, `polygon_two`, and `HexShapeCounts.count_difference` |
| both literal family claims, all bound iterations and all distinct Euclidean starting pairs | proved | kernel-checked `ShannonFixedRadiusCircleVertices.ShannonA374338.result` and `MarkeyFiveSiteGrowthDifference.MarkeyA400701.result`; Markey is this dossier's resolution node and Shannon belongs to `Problems/a374338-circle-vertices.md` |

### What the settlement shows

The decisive mechanism is the exact circle-to-lattice bridge followed by the expanding-hexagon invariant and congruence-class counting. It proves the formulas uniformly over all distinct starting pairs, so no normalization of the initial distance or orientation is an extra hypothesis. The same structural result covers seed lengths 2 and 5; `HexShapeCounts.count_difference` gives the symbolic $4n+7$ polygon-count gap. The six-site computation disproves an unrestricted use of the same base hexagon at step 2. It is outside the nominated seeds and is not a counterexample to either settlement. The tests at lengths 3 and 4 establish only their displayed finite bases. Region and edge formulas, generating functions and arbitrary-seed all-index classifications remain open here. Source formulas depending solely on the proved vertex count may use it as a theorem; no claim about their independent geometric counts follows.

The literature screen on #21460 distinguishes exact finite-time claims from asymptotic threshold-growth results and reports no settlement in the searched scope. Its citation-discovery completeness is ASSUMED-UNVERIFIED.

## ASSUMED-UNVERIFIED

Literature completeness remains ASSUMED-UNVERIFIED: the preregistration records unavailable or rate-limited citation indexes. Mathematical proofs and numerical experiments are distinct evidence. The supplementary scope script has no verified immutable publication revision. Escape registration remains unfinished under #22020.
