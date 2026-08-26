# Proof-topology finite-model replay and PR #2904 correction

## Correction

PR #2904 did not contain a finite adversarial replay file or its executable.
The earlier statement that this material had been synchronized to that PR was
incorrect. The changed-path list for PR #2904 contains only the Lean modules and
freeze records described in that PR.

## Status and boundary

This replay is supplementary counterexample search. It is not a substitute for
Lean elaboration, kernel checking, axiom inspection, or repository admission.
The enumerations below test finite instances of the same abstract statements
formalized in the pull request.

## Original replay

| Statement family | Cases checked |
|---|---:|
| Alexandrov principal-open and principal-closed laws | 285 |
| DAG reachability partial order | 75 |
| Depth filtration | 269 |
| Dominator cut | 268 |
| Monotone labels along reachability | 4,637 |
| Partition topology versus readout kernel | 90 |
| Primitive escape versus strict refinement | 348 |
| Productive escape | 2,048 |
| Residual separation | 644 |
| Semantic-closure topology invariance | 52 |
| Target factorization versus continuity | 84 |
| **Original subtotal** | **8,800** |

## Completion replay

The completion pass exhaustively enumerated finite readouts, targets, preorders,
maps, and the minimal complete Boolean decoder catalog needed by the new direct
bridge theorems.

| Statement family | Cases checked |
|---|---:|
| Factorization versus partition-open inclusion | 1,528 |
| Residual antitonicity under readout refinement | 12,752 |
| Redundant coordinate versus unchanged join topology | 1,528 |
| Faithful observation versus discrete partition topology | 140 |
| Multi-target separation-deficit union law | 668 |
| Alexandrov continuity versus monotonicity | 24,872 |
| Alexandrov inseparability versus mutual reachability | 278 |
| Complete diagonal topological settlement | 2 |
| **Completion subtotal** | **41,768** |
| **Combined total** | **50,568** |

Result:

```text
No counterexample found.
```

The diagonal settlement checks use the minimal complete catalog with two
addresses, a one-point coordinate type, Boolean output, and Boolean negation as
the fixed-point-free twist. They verify simultaneously that the diagonal lies
outside the listed decoded catalog, does not factor through the latent readout,
has a nonempty target defect, and strictly refines the joined partition topology.

The relative-negation and involution modules also include explicit finite
Boolean witnesses inside Lean. Their authoritative status, like every other
statement in this report, is determined only by the repository's Lean and
admission gates.
