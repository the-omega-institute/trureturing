---
slug: zhang-ying-schmid
bibkey: zhangyingschmid2026quantifiers
doi: 10.22331/q-2026-07-30-2180
url: https://arxiv.org/abs/2504.02944v3
triage: theorem
motivation_gids:
  - D5/S3/QuantumContext/FinitePreparationCertification.result
---

# Finite preparations certify nonclassical measurements

## Problem

Zhang, Yīng and Schmid, *Quantifiers and witnesses for the nonclassicality of measurements and of states*, Conjecture 1, Section 4.3, arXiv:2504.02944v3, asks:

> A finite number of preparations is sufficient for the theory-independent certification of any nonclassical measurement with a finite number of outcomes (through the violation of some noncontextual inequality).

The settlement is **Proved**, under the literal conventions preregistered in [#23171](https://github.com/the-omega-institute/trureturing/issues/23171). For every positive finite Hilbert dimension $d$, positive finite outcome count $m$, and POVM $M$, nonclassicality means that no single discrete summable ontological model works for all density matrices. There exist finitely many density matrices $\rho_a$, real coefficients $w_{ab}$, and a real number $c$ such that

$$
\sum_{a,b}w_{ab}p_{ab}\le c
$$

for every noncontextual table $p$ preserving all preparation and effect identities, whereas

$$
c<\sum_{a,b}w_{ab}\operatorname{Re}\operatorname{Tr}(\rho_a M_b).
$$

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Any nonclassical finite-outcome measurement | `claim` quantifies over positive `d`, positive `m`, `M`, `IsPOVM M`, and `¬ Classical M` | Every positive finite dimension and outcome count |
| A finite number of preparations | The existential `n` and density-matrix family indexed by `Fin n` | The family may depend on `M`; no uniform bound |
| Theory-independent certification | The inequality holds for every `NoncontextualTable ρ M p` | Complete operational identities, with no matrix-factorization assumption for ontic assignments |
| Violation of some noncontextual inequality | Real `w` and `c`, universal noncontextual upper bound, strict Born violation | An operational inequality, with both clauses retained |
| Definition 3 responses | `responsePolytope` | Nonnegative, normalized, and annihilating every real effect identity |
| Definition 1 ontological assignments | `NoncontextualTable` | Arbitrary discrete ontic type, `HasSum` normalization and reproduction, every finitely supported real preparation identity |
| Definition 2 classicality | `Classical` | One model for the subtype of all density matrices |

The four public definitions retain the preregistered expressions. Finite indexing by `Fin` is a relabeling. One certain normalized output per preparation setting gives the normalized multi-state specialization. Real parts give the real Born probabilities on the source's positive Hermitian objects. Continuous measurable ontic models are outside these conventions. No source clause is dropped.

## Motivation

The source distinguishes witnesses using quantum descriptions from operational noncontextuality inequalities. Appendix E supplies a finite noncontextual experiment whose description-dependent witness is nevertheless below the associated quantum threshold. The conjecture requires finite preparations giving an inequality valid for every allowed noncontextual table. The settling declaration is `D5.S3.QuantumContext.FinitePreparationCertification.result`.

## Gap

The source's finite response-vertex characterization alone does not supply one preparation model common to all states. Separate models on finite families must be compared on the same response carrier while preserving every linear preparation identity. The remaining issue is joint consistency across preparation families, followed by strict separation of the finite Born table.

## Route

Write $P_M$ for the nonnegative normalized responses annihilating all effect identities. An intersection of kernels is a linear subspace, and the response set is a simplex fiber over its quotient. The imported `FiniteSimplexFiberPolytope.simplexFiber_isPolytope` yields a finite set $V$ with convex hull $P_M$.

For each original response $\xi_\lambda$, choose coefficients $t_{\lambda v}\ge0$ with $\sum_v t_{\lambda v}=1$ and $\xi_\lambda=\sum_vt_{\lambda v}v$. Define compressed preparation weights by

$$
\nu_a(v)=\sum_\lambda t_{\lambda v}\mu_a(\lambda).
$$

The bound $0\le t_{\lambda v}\le1$ gives summability by domination by $\mu_a$. Finite-sum interchange preserves normalization, every preparation identity, and every table entry. `compress_table` proves this for arbitrary preparation index types and arbitrary discrete summable ontic spaces.

For the fixed finite carrier, all weights lie in a product of finite probability simplexes. Each table-entry equation and each finitely supported preparation identity defines a closed constraint. A model on a finite family extends outside that family by a fixed probability vector. Finite unions of preparation families verify the finite-intersection property. Product compactness gives a common model (`fixed_global_of_finite`). Applying this to all density matrices proves the finite-obstruction contrapositive (`finite_obstruction`). The imported `CartesianVariance.density_nonempty` supplies a density matrix for positive dimension and is used to establish nonemptiness of the chosen response carrier.

For a finite preparation family, `preparationWeights_compact` and `preparationWeights_convex` prove that normalized nonnegative weights satisfying all preparation identities form a compact convex set. `fixed_table_iff_image` identifies noncontextual tables on the fixed carrier with its image under `mulRightLinearMap`. Compression and `fixed_table_model` identify this image with all allowed noncontextual tables. Strict Hahn–Banach separation yields a functional and a strict bound. The published owner `FiniteBayesRiskDominanceCriterion.continuous_linear_expansion`, applied by `dual_table_coordinates`, gives the finite coordinate coefficients of that functional. `separate_finite_table` supplies the required inequality, and `result` combines it with the finite obstruction.

## Falsifier

A counterexample under the stated conventions would be a positive finite-dimensional POVM with no common discrete summable noncontextual model, for which every finite density-matrix family admits such a model, or a finite Born table outside the compact convex noncontextual image that admits no strict linear separation. The kernel-checked `result` rules out these alternatives in the formalized domain. A measurable integral model in a different ontic category is not a counterexample to the discrete `HasSum` statement.

## Evidence

The Lean module is `D5/S3/QuantumContext/FinitePreparationCertification.lean`; its Blueprint Scribe displays the full definitions and expanded settling proposition. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`. The proof shape is `bind-only`; its admission basis is `open-problem-resolution (#23171; Proved)`. No independent escape witness is claimed. The published coordinate-expansion owner keeps its mathematical statement and proof.

Escape audit is unfinished for `FinitePreparationCertification.result` and the published `FiniteBayesRiskDominanceCriterion.continuous_linear_expansion`; [#25274](https://github.com/the-omega-institute/trureturing/issues/25274) identifies both targets and the missing source-bound realization/reconstruction and variation/sensitivity evidence. No Reg mirror is delivered and no validated registration is claimed.

### Exact finite experiment

The experiment is [finite-preparation-certification at immutable revision `73d9b0e69a1a2be0fb19b6234c6cdb23adb0ed4a`](https://github.com/the-omega-institute/trureturing-experiments/tree/73d9b0e69a1a2be0fb19b6234c6cdb23adb0ed4a/docs/reports/finite-preparation-certification). In that directory, `python3 check.py` exits 0 with `ALL_CHECKS_OK`. The script SHA-256 is `2be0bd49ce6ad73d4aa024b733319c070adb27ecce3f5c2a9bf820f5b321c538`.

All arithmetic is integer or rational. The tested scope is all reduced rational $a,b,\eta\in[0,1]$ with denominators at most 6 and $a^2+b^2\le1$: 1,677 cases, comprising 1,480 nonzero-noise models, 68 violations and 129 zero-noise models. The 21 boundary cases are included among the 1,480 models. All 16 preparation-cone-ray/response-vertex pairs satisfy the mass-normalized bound. The checker also verifies finite detection for the 95 distinct rational $\eta$ with denominator at most 32 and $2\eta^2>1$, using four rational pure preparations each; compression of 25 rational responses to four fixed vertices; and Appendix E's table, explicit model, and preparation/effect identity bases. These computed results do not certify the universal compactness argument.

## Triage

The evidence labels below distinguish kernel-checked declarations, exact computation, and open extensions. All Lean names in this table have prefix `D5.S3.QuantumContext.FinitePreparationCertification`.

| Item | Status | Evidence kind and precise scope |
| --- | --- | --- |
| Every nonclassical finite-outcome measurement has a finite preparation obstruction and a strictly violated noncontextuality inequality under the unchanged conventions | **Proved** | Kernel-checked `finite_obstruction`, `separate_finite_table`, and public `result` |
| Any arbitrary discrete summable ontic model can be compressed to one finite response carrier while preserving every finite preparation identity | **Proved** | Kernel-checked `response_finite_hull` and `compress_table`; preparation index type and discrete ontic type are arbitrary |
| Finite consistency on that fixed carrier gives one common global model; finite noncontextual tables are a compact convex linear image | **Proved** | Kernel-checked `fixed_global_of_finite`, `preparationWeights_compact`, `preparationWeights_convex`, `fixed_table_iff_image`, with the two directions established in `separate_finite_table` |
| The compactness helper allows arbitrary preparation index sets and arbitrary target tables, with no POVM assumption; the public conjecture retains every original hypothesis | **Proved** | Kernel-checked signature of `fixed_global_of_finite` and the complete signature of `result : claim` |
| Checker exit 0 and `ALL_CHECKS_OK`: 1,677 rational rectangle cases (1,480 nonzero-noise models, 68 violations, 129 zero-noise models; 21 boundary cases included), 95 rational detections, compression of 25 responses to four vertices, Appendix E fidelity | **Computed** | The exact finite experiment above; command, immutable revision, SHA-256, exit code, counts, and parameter bounds are stated there |
| Optional $k d^2+1$ pure-preparation bound | **Open** | Outside the binding claim; no declaration here proves a quantitative or pure-preparation bound |
| Continuous measurable ontic models, infinite outcomes, uniform quantitative preparation/noise/sample bounds | **Open** | Outside the discrete finite-outcome proof; no measurable-integral or uniform quantitative bridge is supplied |
| Complete literature novelty outside the bounded screened corpus | **Open** | Literature completeness is `ASSUMED-UNVERIFIED`; absence in a bounded screen does not establish global novelty |

### What the settlement shows

**Proved, kernel-checked:** the decisive mechanism is common finite response compression followed by compactness of the simultaneous preparation constraints and strict separation of the finite table. This produces an actual operational inequality, beyond a description-dependent witness. The internal compactness statement permits arbitrary preparation index sets and arbitrary target tables, and does not assume the preparation matrices are density matrices or that $M$ is a POVM. The public theorem retains the complete source assumptions.

**Proved, kernel-checked:** within those conventions, the finite-certification assertion posed in Section 4.3 holds, by `result`. The source's response polytope and finite vertex representation remain prior ingredients. The proof gives no quantitative strengthening of the source's noise robustness, no uniform preparation count, and no sample-complexity estimate. Sharpness, the optional pure-preparation bound, and continuous measurable extensions remain **open** here. The finite checker supplies only the **computed** instances stated above.

### Literature status

The source's definitions and response-vertex decomposition are literature-attested. The bounded screen recorded in #23171 covers identified journal/Semantic Scholar citations, relevant later-author texts, arXiv phrase searches, and classical finite-polytope/simplex-embedding tools, including Gitton–Woods and Selby et al. No target settlement was located in that screened corpus (`not-found-in-searched-scope`). Gitton–Woods' reduced-space finite-approximation results and the existing finite-input polytope theorems have different stated hypotheses; they are credited as prior tools rather than asserted settlements of this precise global-to-finite claim.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. General-web and MathDB coverage, blocked MathOverflow retrieval, local-index freshness, an unidentified citing record, the Barnum–Lami manuscript and recent author-talk materials are not independently complete. No inaccessible record is treated as an empty search. The source/literature assessment in #23171 is attributed to its producers; the kernel proof and exact finite experiment have the evidence described above. The unfinished escape audit is separate from the mathematical settlement and is tracked in #25274.
