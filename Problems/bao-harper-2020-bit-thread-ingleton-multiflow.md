---
slug: bao-harper-2020-bit-thread-ingleton-multiflow
bibkey: baoharper2020hypergraphs
doi: 10.48550/arXiv.2012.07872
url: https://arxiv.org/abs/2012.07872v1
triage: theorem
motivation_gids:
  - D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.result
---

# A max multiflow need not reproduce the Ingleton entropy combination

## Problem

Ning Bao and Jonathan Harper, *Bit threads on hypergraphs* (2020), arXiv:2012.07872v1, Conjecture 1, Section 3.2, `BT_Hyper.tex` lines 419–424:

> For a given geometry consider a linear combination of entropies $R(S)$. If $R(V)\geq0$ for all multiflows and there exists a multiflow such that $R(V)\neq0$, then for all max multiflows
>
> $R(S)=R(V).$

The source is the TeX member `BT_Hyper.tex` from the [v1 source archive](https://arxiv.org/src/2012.07872v1), md5 `e001e89a911f72e1614de54e82230780`. Lines 409–416 define the same linear combination on entropies and subflows; the footnote at line 417 expressly includes ordinary 2-graphs among the geometries. The definitions and source locators are collected in [the literature note](../Library/Entropy/baoharper2020hypergraphs.md).

Issue [#22654](https://github.com/the-omega-institute/trureturing/issues/22654) fixes the finite-graph reading. Let $X$ be any finite vertex set, $k$ any natural number, $b:\mathrm{Fin}\,k\hookrightarrow X$ an injective boundary labelling, and $c:X\times X\to\mathbb R$ a symmetric capacity function with $c(u,u)=0$ and $c(u,v)\ge0$. For each boundary region $I$:

- $S_I$ is the minimum of $\sum_{u\in W,\,v\notin W}c(u,v)$ over cuts $W\subseteq X$ containing precisely the boundary vertices labelled by $I$.
- A multiflow consists of real pair flows $f_{ij}$ and thread numbers $N_{ij}$, using $i<j$ once for each unordered pair. Each such flow is antisymmetric on vertex pairs, has zero divergence away from $b(i),b(j)$, and has divergences $N_{ij}\ge0$ and $-N_{ij}$ at these two endpoints. On every ordered vertex pair, $\sum_{i<j}|f_{ij}(u,v)|\le c(u,v)$.
- $V_I$ sums $N_{ij}$ over unordered pairs with exactly one endpoint in $I$; a max multiflow is a multiflow satisfying $V_{\{i\}}=S_{\{i\}}$ for every boundary index $i$.
- For arbitrary real coefficients $\alpha_I$, write $R(x)=\sum_I\alpha_Ix_I$.

The assertion `claim` is that for every such choice of $X,k,c,b,\alpha$, if $R(V)\ge0$ for every multiflow and $R(V)\ne0$ for some multiflow, then $R(S)=R(V)$ for every max multiflow. The result is its negation.

## Motivation

Bao and Harper seek a bit-thread interpretation of entropy inequalities on hypergraphs. A max multiflow computes all singleton entropies simultaneously, but the source cautions: “In general the subflows associate to higher party regions will not be maximal.” (`BT_Hyper.tex` line 122.) Conjecture 1 proposes that suitable linear combinations can nevertheless be computed exactly by every max multiflow. The paragraph following the conjecture singles out the Ingleton combination as satisfying its hypotheses and proposes using the equality to deduce entropy inequalities.

## Gap

The literature check recorded in #22654 is bounded:

- The v1 TeX contains the quoted conjecture and explicitly includes 2-graphs.
- The preregistration records the orchestrator's search finding no existing repository issue, module, Library note or dossier on this source or conjecture.
- The search-fg report in #22654 records screening the ten citing works listed by INSPIRE, including Jonathan Harper (2021), arXiv:2107.10276, together with arXiv searches and the published open-problems page, without finding a settlement of Conjecture 1.

`not-found-in-searched-scope`.

## Route

Label the five boundary vertices $A,B,C,D,E$ and the centre $O$. The module uses $X=\mathrm{Fin}\,6$, boundary embedding `Fin.castSuccEmb`, and labels $A,B,C,D,E,O$ by $0,1,2,3,4,5$. Its `starCapacity` gives $OA,OB,OC,OD$ capacity $1$ and $OE$ capacity $2$, symmetrically, with every other capacity zero. Choose

$R(x)=x_{AB}+x_{AC}+x_{AD}+x_{BC}+x_{BD}-x_A-x_B-x_{CD}-x_{ABC}-x_{ABD}$.

1. **The thread combination.** `ingleton_combo` expands this functional for every real region function on the five boundary indices. `combo_identity` gives $R(V)=2N_{AB}+2N_{CD}$ for every real family $N:\mathrm{Fin}\,5\to\mathrm{Fin}\,5\to\mathbb R$, without a feasibility assumption. For every $f,N$ satisfying `IsMultiflow starCapacity Fin.castSuccEmb f N`, `star_nonnegative` uses the nonnegativity of these two thread numbers to give $R(V)\ge0$.
2. **The cuts.** Write $w(I)$ for the sum of the capacities of the boundary spokes in $I$. For every boundary region $I$ and vertex cut $W$ satisfying $b(i)\in W\leftrightarrow i\in I$ for every boundary index $i$, `star_cut` gives cut capacity $w(I)$ when $O\notin W$ and $6-w(I)$ when $O\in W$. `star_cut_values` proves $S_I=\min(w(I),6-w(I))$ for every boundary region $I$: both centre placements are admissible, and every admissible cut has one of these two capacities. `star_min_combo` consequently gives $R(S)=0$ for this star and this functional.
3. **A max multiflow.** `witnessThreads` selects one thread on each of $AB,CE,DE$, with all other entries zero; `witnessFlow` routes each selected thread through $O$, assigning the negative on reversed edges. For these exact capacities, boundary embedding, flows and thread numbers, `witness_is_multiflow` proves all multiflow constraints, and `witness_max` proves all five singleton equalities. `star_witness_combo` gives $R(V)=2$ for this witness.
4. **Contradiction.** `star_symmetric`, `star_loopless` and `star_capacity_nonnegative` verify all capacity hypotheses for this exact star. The witness is both a nonzero-valued multiflow and a max multiflow. Applying `claim` with these data would identify $0$ with $2$; `result` concludes `¬ claim`.

## Falsifier

The refutation would not settle the source conjecture if the graph quantities, multiflow conditions or meaning of “max” differed in a material way from the source's 2-graph reading. The module uses a finite nonempty collection of admissible cuts: the boundary image of $I$ is always admissible, so `minCut` is an attained finite minimum. It uses one orientation per unordered boundary pair and counts each crossing pair once in `subflow`. `IsMaxMultiflow` requires precisely the singleton saturation condition; it does not add saturation of larger regions. The explicit witness uses boundary vertices only as endpoints and obeys the shared absolute-load bound.

The source writes a linear functional as a difference of sums with nonnegative coefficients; `claim` uses arbitrary real coefficients, equivalently their positive and negative parts. All of the star's nonzero edge capacities are positive. The nonzero-value premise is satisfied by the same max multiflow that violates the proposed equality. No general existence theorem for max multiflows is needed for this instance. The refutation concerns the equality conjecture: its entropy combination is zero, so it does not violate Ingleton's inequality.

## Evidence

The canonical source is `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:da96847e4478e9b5f999e986daba64d2692a19bcab226703f2450cfc36314ca2`;
- `claim`: `sha256:56f8d422f17f537b95acc1b1edafcb5ca7a51fd66c0277c25bc2507b1f87e053`.

## Triage

Tier 1 conjecture of a 2020 arXiv paper, preregistered in issue #22654 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every finite vertex set, every finite injectively labelled boundary, every symmetric loopless nonnegative real capacity function and every real linear functional $R$, nonnegativity of $R(V)$ on every multiflow and a nonzero value on some multiflow imply $R(S)=R(V)$ on every max multiflow.

**Computed, not formalized** (dossier seat, exact enumeration): the integral max multiflows of this star were enumerated; the enumeration covers integral assignments only.

**Argued, not formalized.**

- *Mechanism.* Singleton saturation fixes the total number of threads incident to each boundary, leaving freedom in their pairing. The Ingleton functional detects the pairing through `combo_identity`, which applies to every real family of five-boundary thread numbers. For the explicit star and witness, `witness_max` supplies singleton saturation while `star_min_combo` and `star_witness_combo` give $R(S)=0$ and $R(V)=2$. Thus nonnegativity on all multiflows imposes no equality between the two linear combinations.
- *The missing structure.* For any graph and multiflow in the finite-graph reading, put $\delta_I=S_I-V_I$. Summing the conservation equations for the crossing pairs, each oriented out of $I$, expresses $V_I$ as their outward flux through any admissible cut. The shared absolute-load bound makes this flux at most that cut's capacity, hence $\delta_I\ge0$. Nonetheless, $R(S)-R(V)=\sum_I\alpha_I\delta_I$ has coefficients of both signs. Equality requires cancellation of these weighted deficits; nonnegativity of $R(V)$ does not supply it. On a max multiflow the singleton deficits vanish; singleton saturation alone does not force all larger-region deficits to vanish or their signed sum to cancel.
- *Sufficient conditions that survive.* If one common multiflow saturates every region with nonzero coefficient in $R$, substitution gives equality term by term. In particular, a functional supported only on singleton regions equals its entropy value on every max multiflow, directly by the singleton equalities in `IsMaxMultiflow`. Neither observation asserts existence of a multiflow simultaneously saturating additional regions.
- *A weaker local statement.* On the same star, route one thread on each of $AC,BE,DE$ through $O$. Each of $A,B,C,D$ then has one incident thread and $E$ has two, so the spoke loads and singleton subflows equal their capacities and singleton cuts. This is another max multiflow, and `combo_identity`, for its five-boundary thread family, gives $R(V)=0$ because $N_{AB}=N_{CD}=0$. Thus equality is achievable on this star even though it is not true for every max multiflow. A universal replacement of “every max multiflow” by “some max multiflow” is not settled here.
- *Effect on the paper.* The proposed use of Conjecture 1 to infer $R(S)\ge0$ from subflow nonnegativity, in `BT_Hyper.tex` line 426, loses its general justification through the equality. The source's restricted Ingleton derivation at lines 374–393 retains its additional simultaneous two-region saturation assumption. Its two-thread entropy identification at lines 395–399 must retain that assumption: singleton saturation gives $2N_{AB}=S_A+S_B-V_{AB}$, and identifying this with $I(A:B)=S_A+S_B-S_{AB}$ requires $V_{AB}=S_{AB}$. The counterexample has $R(S)=0$, so it supplies no contradiction to Ingleton's entropy inequality itself. The source's max-multiflow existence statements and its separate cyclic-inequality discussion do not depend on Conjecture 1; this settlement does not assess their proofs.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The INSPIRE count, the ten citing full texts, the arXiv searches and the published open-problems page remain the search-fg reports recorded in #22654; those readings have not been independently reproduced. The preregistration's repository-absence check and the Crossref publication search reported in the Library note have not been independently reproduced. The checked arXiv record provides the arXiv-issued DOI above and lists no journal reference or journal DOI.

The integral enumeration and every argument in “Argued, not formalized” are not additional Lean conclusions. The enumeration gives no exhaustive result for nonintegral assignments. A general characterization of deficit cancellation, a universal existential variant of the conjecture, claims restricted to genuine higher-valence hypergraphs, continuum geometries and physical state realizations are not settled by this module. Source-to-formalization correspondence and the analysis of dependencies in the source are textual and mathematical arguments rather than kernel-checked bridges. No independent verification of the source's general Ingleton or max-multiflow existence proofs is claimed.
