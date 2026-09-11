# P68.1 actual-history leaf-source-square identity

This candidate implements only the Definition 13 source filter, the P68 signed source function and finite-support representation, and the P68.1 readout equation. It is an unfrozen, uncovered implementation for caller review. The complete 6,791-line source through P68 remains the overall goal.

Work target: `/Users/auricstudio/trureturing-csa-leaf-square68-0911`. Immutable BASE: `e492280a34dc1f09ac42d23749ad6a90bd223584`. Mathematical source revision: `df31b816bf570ddb71664473d1f7e33e8fcae6f0`; SHA256: `98506d9461a2bf48f586c68a7987d839a8be1d0c3d9e503febbd7bccc2f884bc`. The caller's `route-result-r2.json` supplies the sole module address. The header preserves its anchors, mirrors, generality, and utility order.

Protocol: consensus-rnd:sshx, sole implementation worker, repo-prior-exposed, no same-round peer judgments or opaque process-log reads. Complete CLAUDE.md and agents/CONTEXT.md were read before implementation. No delegation, independent-review claim, finite overall pass budget, or oracle-diversity claim is made.

## Source obligations and exact types

The source lines below refer to the pinned mathematical input, not a re-ingested atom inventory. [declaration-types.json](declaration-types.json) contains the elaborated type of every canonical row, including private and generated declarations. [canonical-module.json](canonical-module.json) copies their canonical kinds, inclusion flags, axiom closure, and identities. The Lean module contains the human-readable exact signatures.

| Source clause | Declaration / representation | Scope |
| --- | --- | --- |
| Definition 13, line 425 onward: fixed arbitrary source set filters selection | `sourceFilter : Set SourceTree → Rich 3 → Rich 3`; `sourceFilterBalanced : Set SourceTree → BalancedRich 3 → BalancedRich 3` | Identical dependent Context; identical archive, current region, attributes and causal relation; original balance proof reused |
| P68 definitions, lines 6675–6686: `z_r` | `sourceCharge : Rich 3 → SourceTree →₀ Int`; `source_charge_apply` | Finite signed-singleton sum over actual selected HF events; coefficient equals the full selected fiber sum and singleton-filter readout |
| P68.1, lines 6688–6694: fixed equal-leaf square sum | `equalLeafSources`; `leaf_square_readout` | All actual `BalancedRich 3`; the fixed set is exactly `range (j ↦ mul (of j) (of j))` |
| First P68 proof, lines 6710–6727: generated occurrences and signed double sum | `leaf_product_fiber_readout` | Outer sum over occurring leaf sources, inner sums over every ordered selected event pair in that source fiber |
| P68 finite-support qualification and natural-index equality | private `support_sourceCharge_subset`, derived `leafCharge`, private `leaf_reindex`, `leaf_square_readout_nat` | Nonzero support is only contained in occurring sources; restriction to leaves precedes reindexing |

There is no public decidability, nonemptiness, finite-set-of-sources, computability, positivity, or per-source balance parameter. Dimension three is the routed source dimension. `SourceTree` is the existing `FreeMagma Nat`, with the existing source/HF representation owner; no second encoding is introduced.

## Search and reuse

[search.json](search.json) records D5 → pinned Mathlib v4.33.0 (`db584cd6d46c92f209a44c0f1c829460d327499d`) → bounded admissible ecosystem searches, completed before local proof writing. Real HTTP Loogle search succeeded; native web tools were absent. The failed Reservoir endpoint is reported as a capability limitation. Repository metadata search is not exhaustive code search. No complete typed CSA coefficient or actual filtered-history edge was found in that searched scope; no admission-basis narrowing was therefore triggered.

The actual product proof directly uses `GeneratedProduct.attributes_generated`, `GeneratedProduct.charge_generated`, `Finset.filter_map`, and `Finset.sum_fiberwise_of_maps_to`. The selected-current/event transport uses `ProductNodes.sum_selectedParents`. The coefficient proof uses `Finsupp.finsetSum_apply`, `Finsupp.single_apply` and `Finset.sum_filter`. The endpoint uses `Finset.sum_mul_sum` and `Finsupp.sum_of_support_subset`. Natural reindexing uses `Finsupp.sum_comapDomain` after restricting to leaf sources. All are exact owners; no generic algebra is reproved.

## Proof shape, admission basis, utility and live use

Proposed module proof shape is **bind-only**. No escape witness or novelty is claimed. The two prospectively registered representation obligations retain **atom-required-bridge** as their proposed admission basis, subject to caller's independent semantic review. Their consumer is the already registered `LeafSquareReadout.leaf_square_readout`. Exact-owner companions are same-module thin bindings with the corresponding rule-11 owner and source obligation; none is proposed as an independent deposit.

The directed consuming derivation is concrete:

1. `leaf_square_readout → leaf_product_fiber_readout`: the first rewrite changes the actual filtered `productBalanced X X` readout into complete ordered occurrence-fiber sums.
2. The support-subset proof permits replacing the final Finsupp sum by the finite set of **occurring** leaf sources. It only removes zero fiber totals. No history or selection is pruned using nonzero support.
3. `leaf_square_readout → source_charge_apply`: its first conjunct replaces each charge coefficient with the literal signed event-fiber sum. `pow_two` and `Finset.sum_mul_sum` then equate that square with the double sum. The consumer performs this substitution and factorization; it does not forward either bridge's statement.
4. `leaf_square_readout_nat → leaf_square_readout` and `leaf_reindex`: `leafCharge` first filters the same source charge to leaves, then precomposes with `FreeMagma.of`. Surjectivity onto that restricted support follows from leaf membership. No surjectivity onto arbitrary source support is assumed.

`source_charge_apply`'s singleton-readout conjunct is the Definition 13 companion interpretation. The square theorem uses its **first** conjunct; the second conjunct is not misreported as a separately live arithmetic dependency.

[reduced-use.json](reduced-use.json) records retention of both bridges and `Finset.sum_mul_sum` after Lean's zeta reduction, beta reduction and recursive `whnfCore` reduction, without delta-unfolding named constants. [LiveUseProbe.lean](LiveUseProbe.lean) checks this. Constant retention alone is not an automatic semantic-liveness or escape-witness certificate; the actual equality chain above supplies the authored live-use argument.

`utility: none` applies to every admitted row: these are definitions and identities for arbitrary histories, source sets and source labels, plus symbolic support/transport/reindexing. They do not certify a finite positive instance, enumerate a bounded class, provide a checker instance, or perform a numerical reduction. The validation-only finite fixtures are outside the routed module and have no admission claim. Per-row source obligations, directed uses, proof shapes, bases and utility reasons are in [declaration-accounting.json](declaration-accounting.json).

## Complete declaration accounting

There are **26 canonical rows**: 5 definitions and 21 theorems. There are **15 included** rows (9 authored public and 6 authored private), and **11 excluded generated** rows. Private does not mean excluded. One excluded generated row is named `ComplementCharge.q.eq_1` but is emitted in this candidate module; it is reported under the canonical module, without claiming an edit to the frozen ComplementCharge owner. All rows have captured canonical identities and exact types; unknown row count is zero.

The axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, new axiom or native-decision axiom is used by the candidate module. [raw-dependencies.jsonl](raw-dependencies.jsonl) comes from the existing canonical Inspector's dependency mode using [dependency-manifest.json](dependency-manifest.json), which explicitly lists only the routed module. [DeclarationTypes.lean](DeclarationTypes.lean) prints its known module constants and types; it is an evidence probe, not an ownership classifier.

[frozen-direct-identities.json](frozen-direct-identities.json) supplies 31 directly referenced frozen-owner constants from an explicit six-module manifest. Thirty have committed accepted declaration identities, read without historical recalculation. The excluded generated `ProductNodes.mem_selectedParents._simp_1` has a current canonical report identity but no entry in the accepted declaration list; its accepted identity and public GID remain null. It is not silently relabeled as a frozen public theorem.

Raw type/value dependency sets, local private/generated expansion, and reduced proof retention are separate evidence products. Auxiliary expansion follows only this module's private/generated **value** references and stops at public declarations; it is not labeled a reduced-live set. Generated equation rows with no captured named consumer are explicitly recorded as such. [module-materials.json](module-materials.json) preserves the exact selected UTF-8 statement strings from the full canonical bundle; [material-index.json](material-index.json) records the copied canonical addresses and plain byte-integrity hashes. Re-encoding each string as UTF-8 gives the exact canonical material bytes. An initial ZIP subset was replaced with this text representation to meet the repository's strict UTF-8 contract.

## Validation and handoff limits

[boundary-contracts.md](boundary-contracts.md) was written before local proofs. [BoundaryProbes.lean](BoundaryProbes.lean) transports four typed names to the existing actual HF carrier. All 17 assertions and their supporting transport proofs pass Lean. They check the full Context identity for arbitrary filters, empty archive/current/selection cases, cancellation with four surviving ordered pairs and contributions `[1,-1,-1,1]`, distinct equal-leaf positive occurrences with four pairs/readout four, and mixed sources with a nonzero nonleaf coefficient excluded from the readout. These are source-boundary probes, not independent admission content.

`make lean-cache-ensure`, focused `make lean`, canonical `make lean-report` (which also runs the full pinned project build), `make emit`, and the final boundary/declaration/live-use probes succeeded. Canonical Lake dependency restoration cloned pinned packages into this worktree's ignored `.lake` directory. A cold dependency warmup was interrupted before restoring the published Mathlib cache; cache restoration returned one unrelated download failure after 8,689 decompressions. The subsequent pinned project build and canonical report succeeded. The source module had intermediate elaboration errors which were repaired; final axiom closure has no placeholder.

The fixed-BASE `make gate ... GATE_ARGS=--skip-engineering` fails at setup with `reason=vacuous` because the caller-owned commit has not occurred and HEAD equals BASE. The direct canonical content check is recorded separately in [commands.json](commands.json). Its initial evidence line-count failure was repaired by compact JSON output, and its binary-material snapshot failure by exact UTF-8 JSON material strings. The final direct check completed with **exit 3: protected-surface change only**. It reported `UTILITY-OBSERVED ... semantics=unverified-by-machine` and the expected missing frozen state; these do not certify semantic admission. The Scribe addition is a protected-surface SL-022 change and requires the caller's normal review/lifecycle treatment. No gate or independent admission approval is claimed. No repeated full preflight, deposit, freeze, cover, ingestion, state/ledger edit, repository Git lifecycle mutation, PR operation or host configuration change was performed. `make emit` refreshed its ignored generated catalog/FILEMAP/DAG outputs; no authoritative FILEMAP or other out-of-scope tracked file changed.

The caller must perform source commit, independent reviews, admission/deposit-uncovered if accepted, all required checks, PR delivery and cleanup. The worker does not cover any of `a593cc377b9cbe44345388cac27e5d35e728ef9b2984dbf55511b4928daa0e34`, `cc2f67e031af25f30307f43bfa3ada88149b34006a2934c3027ff1214e23709f`, or `1fbf9d908cce5104ce7b1e15c62d3ad62bfea7c3974215bcca79abf897390011`: their strengthened syntax/total-expression clauses are larger than this identity. No strict AST, total-expression E membership, exact two-input-leaf theorem, P68.2/3, whole-CSA completion, or ZFC conservativity/model-existence/consistency result is claimed.
