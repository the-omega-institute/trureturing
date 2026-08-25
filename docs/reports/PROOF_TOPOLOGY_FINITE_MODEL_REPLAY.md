# Proof-topology finite-model replay and PR #2904 correction

## Correction

PR #2904 did not contain a finite adversarial replay file or its executable.
The earlier statement that this material had been synchronized to that PR was
incorrect. The changed-path list for PR #2904 contains only the Lean modules and
freeze records described in that PR.

## Scope of this replay

The replay is supplementary counterexample search. It is not a substitute for
Lean elaboration or kernel checking. Small finite models were exhaustively
enumerated for the following statement families:

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
| **Total** | **8,800** |

Result:

```text
No counterexample found.
```

The new relative-negation and involution modules also include explicit finite
Boolean witnesses inside Lean. Their authoritative status is determined only by
the repository's Lean and admission gates.
