---
slug: bonin-2024-shadow-markoff-positivity
bibkey: bonin2024shadowmarkoff
doi: 10.48550/arXiv.2403.07668
url: https://arxiv.org/abs/2403.07668
triage: theorem
motivation_gids:
  - D5/S3/Factorization/BoninShadowMarkoffPositivity.result
---

# Bonin's shadow Markoff positivity region

## Problem

Nathan Bonin, *Conditions of positivity on a shadow Markoff tree*, J. Integer Sequences 27 (2024), Article 24.8.3, arXiv:2403.07668v2, Conjecture 1, asks for the quadrilateral of projective initial shadows that give an integer positive shadow Markoff tree. The source and its literal quotations are recorded in [the Library note](../Library/Factorization/bonin2024shadowmarkoff.md) and preregistration [#17060](https://github.com/the-omega-institute/trureturing/issues/17060).

The precise assertion uses the rooted tree of Sections 2 and 5: start at $(1,\alpha,1,\beta,1,\gamma)$, include the root, apply the mandatory right and left mutations, then every finite word in the two moves. For $(\alpha,\beta,\gamma)\in\mathbb N^3\setminus\{(0,0,0)\}$, every node has all six entries in $\mathbb N$ if and only if

$$\alpha+\beta\leq 2\gamma,\qquad 2\alpha\leq\beta+\gamma.$$

Equivalently, $\gamma>0$ and $(\alpha/\gamma,\beta/\gamma)$ belongs to the rational convex hull of $(0,0),(1/2,0),(1,1),(0,2)$. Natural numbers include zero, as in Equation (8) and the boundary vertices. The result does not quantify over independent root permutations.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| The two directions of Section 5 | `Move` | Left mutates the second pair; right the first |
| Mutation formulas (5), rational division | `step` | Both real and shadow coordinates are literal source expressions |
| Root and mandatory right, left moves, followed by every finite word | `path`, universal word and node quantifiers in `claim` | `List.scanl` includes the initial node |
| All six coordinates in $\mathbb N$, Equation (8) | `IsNatNode` | Six natural witnesses cast to $\mathbb Q$ |
| Nonzero initial natural shadow triple | The three natural binders and nonzero hypothesis in `claim` | Excludes the triple with no projective point |
| Four projective vertices in Conjecture 1 | `quadrilateral` | Rational convex hull in the chart $\gamma=1$ |
| Tree positivity exactly in that region | `result : claim` | Both implications, including the boundary |
| Positive chart denominator | The $0<\gamma$ conjunct of `claim` | Follows from the inequalities and nonzero triple; no extra restriction on the region |

## Motivation

The source's Theorem 1 gives some convex polygon and supplies numerical evidence for the proposed quadrilateral. An exact characterization replaces that unspecified polygon by four explicit vertices and gives actual negative-shadow branches outside it.

## Gap

The preregistration records the arXiv and JIS texts, Bonin's Reims thesis NNT 2026REIMS005, Section 4.5, and the statement “il n'y a pas de démonstration pour l'instant”. Its literature screen includes Semantic Scholar and OpenAlex (zero citing works in those readings), the arXiv and HAL author lists of Bonin and Ovsienko, and arXiv:2503.21872, 2402.19300 and 2507.19080. No proof or refutation was found in that searched scope. Separate JIS citation enumeration was rate-limited. Completeness is `ASSUMED-UNVERIFIED`.

## Route

Write $\sigma=\alpha+\beta+\gamma$. The classical real cubic mutation is supplied by `D5.S3.Factorization.MarkovEquationMutation.markov_equation_mutation`, used in the private `eqn_poly`. The dual identity changes the rational mutation to a polynomial mutation and preserves integrality.

For a real-shadow pair $(a,x)$, put $D_a=3x-\sigma a$. At the node with real entries $(1,2,5)$, the three shifted coordinates are

$$u=2\gamma-\alpha-\beta,\qquad v=4(\beta+\gamma-2\alpha),\qquad w=-29\alpha+4\beta+25\gamma,$$

with $4w=28u+11v$. The private `base_cone`, `cone_poly` and `cone_scan` preserve $0\leq D_a,D_b\leq D_c$ through every finite branch. Together with `path_valid`, `cone_nonneg` and `integral_nonneg_nat`, this proves `sufficient`.

The two constant-direction spines have real recurrences with coefficients $3$ and $6$. Their shadow recurrences have forcings $u$ and $v$, respectively. The private `wronskian_step` gives the identity used by `resonant_negative`; `no_nonnegative_drift` proves that a uniformly negative normalized forcing cannot coexist with nonnegative shadows at every index. The private `necessary` applies this to both spines.

The private `quadrilateral_region` and `region_chart` identify the four half-planes with the four-vertex convex hull. The public `result` combines necessity, sufficiency and the chart correspondence.

The private `scan_invariant`, `cone_scan`, `path_valid`, `sufficient`, `spine_next`, `spine_recurrence_l` and `spine_recurrence_r` are consumed bind-only helpers. After inlining, their proof paths consist of applications of the pinned list scan/fold owners and, where needed, the frozen real cubic, plus polynomial, cast and logical normalization. The content witness is `no_nonnegative_drift`, consumed through `resonant_negative` and `necessary` by `result`. Admission remains `open-problem-resolution (#17060; Proved)`.

## Falsifier

A different move order, omission of the root or mandatory moves, an incorrect rational division, a strictly-positive interpretation excluding zero boundary shadows, or a claim about arbitrary independent root permutations would change the assertion. The statement echo fixes each of these choices. Failure of either implication for one natural initial triple and one actual finite path would refute the delivered assertion; `result` proves both implications for all such triples and paths.

## Evidence

The mathematical source is `D5/S3/Factorization/BoninShadowMarkoffPositivity.lean`; its Scribe is `Blueprint/D5/S3/Factorization/BoninShadowMarkoffPositivity.scribe.cs`. The public mathematical surface contains `Move`, `step`, `path`, `IsNatNode`, `quadrilateral`, `claim` and the sole public theorem `result`. Proof helpers are private. Admission is `open-problem-resolution (#17060; Proved)`, with `utility: none` and `generality: G`. This is a deposit-uncovered settlement with no digestion atom or cover.

The escape audit for `D5/S3/Factorization/BoninShadowMarkoffPositivity.result` is unfinished under [#17538](https://github.com/the-omega-institute/trureturing/issues/17538). No Reg mirror is delivered. The dependent source-family construction alone does not provide the source-bound registration wrapper, exact `sourceSelection` and current binding evidence. It is not a `declared_validated` registration.

### Experiment

[Exact rational checks](https://github.com/the-omega-institute/trureturing-experiments/tree/84c31ea11fdf0563e6cf94aa64e83ac2e5fbcb26/docs/reports/bonin-2024-shadow-markoff-positivity), `check.py`, SHA-256 `f541039479a0ec8af966e29dc5d188562aa45c5ab6e3d5af9b5b9cfbc498e84c`. Command: `python3 check.py` in that pinned directory; exit 0, `ALL_OK`.

The rerun checks all 999 nonzero triples in $[0,9]^3$. All entries are integral on every word of length at most 11 after the mandatory moves. The 359 triples inside the region have nonnegative shadows on all those words. Every one of the 640 outside triples reaches a negative shadow on the selected constant-direction spine, searched to 400 steps; the latest first negative occurs at step 31. The four displayed vertices satisfy the four half-planes and each has two tight edges. The source's Section 5.1 input $(1,0.9,1)$ on `rlrlrlr` has final shadows approximately $4.0831173589030806\cdot10^{19}$, $2.1966347507346\cdot10^{12}$ and $-6.986560783615173\cdot10^{33}$. These finite computations do not establish the unbounded statement; `result` does.

## Triage

Tier 1 published named conjecture, resolution **Proved**. Literature status: `not-found-in-searched-scope`; completeness `ASSUMED-UNVERIFIED`.

### What the settlement shows

| Item | Status and evidence kind | Evidence |
| --- | --- | --- |
| Mechanism: cone propagation supplies sufficiency | Proved, kernel-checked | Private `cone_poly`, `cone_scan`, `sufficient` |
| Mechanism: two forced spine recurrences and negative-forcing obstruction supply necessity | Proved, kernel-checked | Private `spine_recurrence_l`, `spine_recurrence_r`, `no_nonnegative_drift`, `resonant_negative`, `necessary` |
| The two linear forms give the two non-coordinate edges | Proved, kernel-checked | Private `base_cone`, `region_chart` and public `result`; edges $\alpha+\beta=2\gamma$, $2\alpha=\beta+\gamma$ |
| Integrality for arbitrary integer initial shadows, without positivity assumptions | Proved, kernel-checked | Private `path_valid` includes `Integral` for every node |
| Strict positivity after both mandatory moves for every nonzero natural initial triple inside the region | Proved in prose | The derivation below uses the cone and order statements; no separate Lean theorem asserts strict positivity |
| Consequence for the source's Theorem 1 | Proved, kernel-checked | `result` identifies the previously unspecified convex polygon exactly for the rooted tree |
| Arbitrary independent root permutations | Open | Outside `claim`; no uniform positivity assertion is made |
| The q-deformed or super Markoff analogues, including arXiv:2503.21872 Question 5.3 | Open | Different mutation systems; the present invariants supply no proved correspondence |
| Finite numerical evidence | Computed | The pinned experiment entry above, exact tested scope and exit 0 |
| Prior literature resolution | Open as an exhaustive absence claim | The bounded literature reading in Gap found none; completeness `ASSUMED-UNVERIFIED` |

**Strict positivity derivation (proved in prose).** For a nonzero natural initial triple, $\sigma>0$. At every node from $(1,2,5)$ onward, `path_valid` gives $a,b,c\geq1$, while `base_cone` and `cone_scan` give $3x-\sigma a\geq0$, $3y-\sigma b\geq0$, $3z-\sigma c\geq0$. Thus $x\geq\sigma a/3>0$ and likewise $y,z>0$. This includes boundary projective points after the mandatory two moves, even when their initial shadows vanish. No larger permutation-invariant positivity region follows.

The cone argument separates integrality from positivity: integer initial shadows remain integer throughout without either region inequality. Necessity is sharp because failure of either inequality gives a negative term on the corresponding actual spine. The source's numerical quadrilateral claim is a theorem in the rooted scope; claims about other deformations and independent root permutations retain their stated open boundaries.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are not certified by the bounded screen. The experiment covers only its stated finite box, depth and spine bound. The strict-positivity extension is proved in prose above, rather than stated as an additional kernel-checked theorem. The four-slot escape audit remains unfinished under #17538.
