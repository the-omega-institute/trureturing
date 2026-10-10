# Invariant Safety

## Abstract

An inductive invariant makes every finitely reachable state safe.

**Theorem 1.1 (Inductive invariants certify finite executions).**

$$\forall X: \operatorname{Type}, R: X \to \left(X \to \operatorname{Prop}\right),\\I0, J, S: \operatorname{Set}(X),\\I0 \subseteq J \land J \subseteq S \land\\(\forall x, y: X, x \in J \land R(x, y) \Rightarrow y \in J)\\\Rightarrow \forall x0, x: X,\\x0 \in I0 \land \operatorname{ReflTransGen}(R)(x0, x) \Rightarrow x \in S.$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/Safety/InvariantSafety.invariant_safety` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be a transition relation, I0 the initial set, J an invariant, and S the safe set. The hypotheses expose all three invariant conditions: I0 is contained in J, J is contained in S, and every R-successor of a state in J remains in J.

A reflexive-transitive R path represents an arbitrary finite execution. Direct induction with Relation.ReflTransGen.head_induction_on propagates membership in J from the actual initial state to the endpoint, where containment in S gives safety.

The relation need not be deterministic, terminating or confluent. The conclusion concerns each finite path; it asserts no fairness or eventual completion.

## Scoped material preservation

A reusable collaborative Git worktree illustrates how to obtain the one-step premise from effects rather than assuming safety of each successor. Let M, P and J be arbitrary types of immutable material versions, recovery locations and actual jobs. A state has required material R, confirmed remote material D, local support L in M times P, active use U in J times P, and qualified exclusion holders H in J times P. These are mathematical observations of one realization, not an additional stored record. An item is recoverable when it is in D or has some support in L. Safety requires this for every item of R.

A location p is held when some pair (j,p) belongs to H. Qualification at p means that every material item supported there is in D and no job has active use there. This checks all discarded support, including support for items outside R. The stronger invariant combines safety with qualification of every held location. Locations may denote a directory, a private recovery reference or another affected resource; they are not necessarily whole trees. The material relation represents protected obligations and recovery effects; it does not make every intermediate keystroke a permanently required historical version. Mapping an actual edit requires identifying the still-required items and their genuine reconstruction supports.

The elementary relation has seven effects. Entry adds (j,p) to U only when p is not held. Production at an active, unheld location adds a new required version m together with support (m,p). Confirmation adds m to D. Acquisition adds (j,p) to H at an unheld, qualified location. Inheritance adds (k,p) to H from an existing holder (j,p). Exit removes only pairs labelled by the exiting job from U and H. A destructive effect at a held p removes the pairs (m,p) for m in an arbitrary selected cut, without changing R or D. No effect takes safety or the stronger invariant as its enabling condition. Acquisition denotes the final qualification boundary of an operation already protected by real exclusion, rather than a lock-system call. Preliminary lock acquisition or failed inspection authorizes no destructive effect and must leave material intact; it contributes no qualified holder to H.

Each effect preserves the stronger invariant by set membership laws. Production supplies the new item's local witness. Confirmation only enlarges remote retention. Entry and production cannot affect a held location. Acquisition supplies qualification at its new location; inheritance obtains it from the parent holder. Exit removes activity and holders while retaining all material. Destruction leaves an old support witness unless it cuts that pair; in that case qualification supplies remote retention of the item. It also only shrinks the support set, so every surviving held location stays qualified. Applying invariant_safety to this relation, with the stronger invariant as both J and S, proves preservation through every finite cooperative interleaving, including a prefix interrupted between destructive effects.

Exclusion is continuous in this argument. While any holder at p survives, new entry and new material production at p are disabled, and confirmed retention is unchanged or enlarged. After the last holder exits, further destruction requires a fresh acquisition and qualification. Partial destruction therefore needs no rollback assumption. A one-time sample without exclusion has a countermodel: start with an empty qualified location, admit a writer, produce one unconfirmed item there, then delete its sole support using the obsolete sample. The final state loses a required item.

The allowed relation also has nonempty successful cases. A location supporting a remotely retained item can be qualified and removed while a different location has an active writer and an unconfirmed item. A child inheriting the first location's exclusion can survive the parent's exit and perform the destructive effect. Its later exit releases the last holder. Thus preservation permits concurrent work, recovery and actual disposal; it does not require permanent refusal.

## Attributed checkpoints with independent editing

For a checkpoint, fix an authorized set A of file coordinates, a protected set K containing A, and a stable snapshot v. Represent working bytes by w and the shared index's change unit relative to a fixed agreed base by a function k taking either no change entry or a value. At the start of the attributed operation, w agrees with v on K, and each index entry is either absent or is exactly v at a coordinate in A. Existing unrelated staged entries therefore prevent this operation from starting until their ownership is resolved.

During the operation an independent edit replaces w at a coordinate outside K. A staging step replaces k at a coordinate of A with its current working value. Other index insertion and changes to protected working coordinates are excluded throughout the operation. Function update laws prove that working stability and exact index attribution are preserved by these two effects; invariant_safety extends this to an arbitrary finite staging/editing path. If every coordinate of A is staged at the end, an entry equals the snapshot value precisely when its coordinate belongs to A. Under the exact-index consumption premise for commit, the committed change unit therefore contains only the stable authorized changes.

The boundary includes a countermodel: insert an unrelated entry into k between staging and commit. Individual index updates can each be mutually exclusive, yet the final index violates attribution. Exclusion must span initial index inspection, snapshot stabilization, staging, exact-diff inspection and commit consumption. Working bytes outside the protected footprint may still change. Deletion entries can be represented by a value in the value type; absence from the change unit is a separate index option. Unmerged stages and a changing base require additional representation and coordination; they cannot silently be collapsed into this function.

Semantic authorization can read other coordinates. K must contain the target and both states' actual read sets. `D5/S3/ConceptDynamics/Governance/TwoStateLocalityIncrementalPreservation.two_state_locality_yields_incremental_preservation` supplies equivalence of such a local property under independent editing: equality to the same snapshot gives endpoint byte equality on K, hence an unchanged target and no changed dependency there. The protected set can be strictly larger than the staged set while a third coordinate changes. Disjoint file names alone do not establish independence of read-sensitive operations. `D5/S0/Rewriting/HindleyRosen.reflTransGen_commute_of_strong_commute` lifts the commuting squares of unconditional disjoint-coordinate writes to arbitrary finite write blocks. Neither result supplies a merge procedure for overlapping edits.

## Exit, durability and the realization boundary

For distinct jobs j and k, exit of j leaves every active-use and holder pair labelled k unchanged. An inherited descriptor is represented by a holder pair for the child, rather than by the parent's continued existence. Exit also leaves R, D and L unchanged. Even an exit leaving no activity and no exclusion holder can leave a required item only locally supported. Automatic release establishes no publication.

For finite material sets, `D5/S3/ConceptDynamics/OperationalTuition/ArtifactSufficiencyAndKillLoss.artifact_sufficient_iff_every_kill_zero_byte_loss` gives the separate complete-local-loss boundary: with artifact set D and session set equal to all local material, zero required loss after erasing the latter is equivalent to R being contained in D. Its insufficiency direction exhibits nonempty loss. In this application local Git commits belong to local support until confirmation, even though they are persistent on local disk. A single participant's exit does not perform this erasure.

The substitution into Git and host operations has explicit obligations. Material versions must include working and staged bytes, untracked or unknown ignored content, private refs and reflogs, unfinished operation data, and any other recovery handle removed by the actual effect. Actual use must be represented at every exclusion scope that it intersects. Child paths, common Git state and private references cannot be treated as independent coordinates when an operation's effects overlap them. A support pair means a genuine reconstruction route, including required metadata and object dependencies. Confirmation means that a fresh remote observation establishes retention of the required exact commit and material; a successful process exit, push invocation or stale tracking ref is insufficient. Retention must remain valid through each effect relying on it. A published commit supplies a rebuild source only if its complete reconstruction relation and toolchain premises also hold.

Job identities and descriptor inheritance must match actual surviving processes across hosts. Exclusion must cover every conflicting edit, Git-state mutation and new entrant through the final destructive effect, including children that outlive a parent. Normal task finalization closes admission of its new writers and gathers its existing writers before taking a stable authorized snapshot; other participants remain represented. Abnormal exit changes no publication fact and requires fresh observation before another destructive operation. These are realization premises, not consequences of the abstract theorem.

Identity checks, current and main checkout protection, retained nested registrations, intentional locks and independent cache-use guards are additional conjuncts of engineering eligibility. They cannot be inferred from material safety or exclusion alone. Unknown inventory, activity or remote retention supplies no qualification proof; leaving it in place and using a compatible alternative workspace preserves the unresolved support. Cleanup of local refs, orphan branches and temporary directories has the same material obligation at its own affected scope. This application asserts neither universal Git/OS correctness nor remote availability, eventual publication, reconstruction progress or fairness.

## References

- Truth anchor: `D5/S0/Rewriting/HindleyRosen.reflTransGen_commute_of_strong_commute`
- Truth anchor: `D5/S0/Rewriting/Safety/InvariantSafety.invariant_safety`
- Truth anchor: `D5/S3/ConceptDynamics/Governance/TwoStateLocalityIncrementalPreservation.two_state_locality_yields_incremental_preservation`
- Truth anchor: `D5/S3/ConceptDynamics/OperationalTuition/ArtifactSufficiencyAndKillLoss.artifact_sufficient_iff_every_kill_zero_byte_loss`
