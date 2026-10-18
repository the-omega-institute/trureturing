# Compressed preorder control

## Abstract

A finite binary path determines the complete pending preorder frontier.

A source is a nonempty finite ordered full binary tree with Boolean leaves. An address is a finite Boolean list, with false for left and true for right. Reports retain their addresses and four-valued replies in chronological order.

**Definition 1.1 (Pending right siblings).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.rightsPending`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.rightsPending` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each left edge in p, take the prefix before that edge and append a right edge. List these addresses from the deepest such edge to the shallowest. The list describes the unvisited siblings mathematically; it is not a field of the cursor.

**Definition 1.2 (Advance after a closed node).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.nextPath`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.nextPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Search for the last left edge of p. If it exists, replace it by a right edge and delete all subsequent edges. Otherwise return none. The recursion examines only p.

**Definition 1.3 (The frontier represented by a cursor).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.pending`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.pending` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cursor none represents the empty frontier. A cursor some(p) represents p followed by rightsPending(p).

**Definition 1.4 (One structural step).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.cursorStep`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.cursorStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A branch reply at p moves to p followed by a left edge. Every other reply moves to nextPath(p). Actual source traversal has no absent replies; handling absent as an error is a separate instruction rule.

**Definition 1.5 (Path-selected report sequences).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.CursorRun`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.CursorRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty sequence leaves its cursor unchanged. A nonempty sequence at some(p) must first report p, and its remaining reports start at cursorStep(p,r). The relation has no hidden tree, pending-subtree stack, or acquired history in its transition rule.

**Definition 1.6 (Actual finite prefixes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.ActualCursorPrefix`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.ActualCursorPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial cursor is some(empty address), with no reports. A cursor at p reads the actual source at p and advances by cursorStep. Histories label this relation and are not selector arguments.

**Theorem 1.7 (Exact actual preorder and compressed frontier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.reachable_compressed_frontier_and_trial_simulation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.reachable_compressed_frontier_and_trial_simulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every source u, the complete acquisitionTrace([],u) is a CursorRun from some(empty address) to none. For every cursor c and history h reached by ActualCursorPrefix(u,c,h), h is a prefix of that complete trace, its existing acquisition frontier equals pending(c), and it is a CursorRun from the initial cursor to c. Further, for every decomposition of the complete trace as h followed by report a and suffix s, h is a CursorRun ending at some(a.address), its frontier is exactly a.address followed by rightsPending(a.address), and s is a CursorRun from cursorStep(a.address,a.reply) to none.

The key address identity says that pending(nextPath(p)) is exactly rightsPending(p). Appending a left edge exposes its sibling before all earlier pending siblings. Thus a path step agrees with the independently defined acquisitionStep for every reply. The established actual acquisition execution then supplies the complete path-selected sequence. Induction on actual reads retains a suffix of that sequence, so every actual prefix has the same next query and the same pending queue.

**Definition 1.8 (Seven instruction modes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.Mode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.Mode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The modes, in order, are VALUE, GUARD, POLL, UPDATE, HALT0, HALT1 and ERROR.

**Definition 1.9 (Intermediate fields).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.Control`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.Control` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A control retains only its finite address p, its length s, the branch and leaf counts b and l, candidate index j, parity bit a, and mode mu. No source description or report history is a field.

**Definition 1.10 (Installed constants).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.Parameters`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.Parameters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One controller fixes the positive source size h, starting offset start, last candidate index last, polling literal depth pollDepth and whether the active polling modes are available.

**Definition 1.11 (Canonical exceptional controls).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.canonical`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.canonical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A canonical control sets every field except the specified mode to zero or the empty address.

**Definition 1.12 (Fresh trial).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.fresh`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.fresh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A fresh trial has root VALUE mode, the specified candidate index j, and zero length, counters and parity.

**Definition 1.13 (Mode before a node query).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.queryMode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.queryMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At offset zero or at the root, begin in VALUE. Otherwise begin in GUARD.

**Definition 1.14 (Field conditions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.Valid`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Normal controls require s equal to the path length, s and b less than h, l at most h and j at most last. GUARD additionally requires positive offset and a nonempty path. POLL and UPDATE must be canonical and active. Halt and error controls must be canonical.

**Definition 1.15 (Virtual node successors).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.virtualDelta`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.virtualDelta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A virtual absent reply selects canonical ERROR. A branch reaching the h-th branch resets the trial and increments j if another candidate is available. Other branches descend left only within the path and branch bounds. A leaf increments l and updates parity; nextPath selects the next query. At the end, exactly l+1=h and b=h-1 select canonical HALT with the new parity bit. A saturated leaf counter or any failed condition selects ERROR.

**Definition 1.16 (Total source primitive rows).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.controlProgram`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.controlProgram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

VALUE reads p followed by halfCeil(start+j) right edges and applies decodeLabel followed by virtualDelta. GUARD reads the parent followed by floor((start+j)/2)+1 right edges; acceptance changes only its mode. POLL reads the installed right-ray literal: absent selects UPDATE, alpha starts candidate zero, and the other replies select ERROR. UPDATE performs one genuine update and returns to POLL. The two canonical halt modes halt; invalid controls and ERROR read the root and select canonical ERROR.

**Definition 1.17 (Even polling threshold).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.alignmentBudget`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.alignmentBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural h and T, B=alignmentBudget(h,T)=2 halfCeil(T+2h). Thus B is even and at least T+2h.

**Definition 1.18 (The installed active constants).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.activeParameters`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.activeParameters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source size is h, the starting offset is B-2h+1, the last index is 2h-1, the polling depth is B/2, and active mode is enabled, where B=alignmentBudget(h,T).

**Definition 1.19 (Fields at a mathematical report prefix).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.atPrefix`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.atPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For candidate j, report prefix H, current address p and mode mu, this comparison control has path p, length equal to the length of p, branch and leaf counts of H, candidate j, and parity equal to the beta count of H modulo two. It is used to relate controls to traversal prefixes; the instruction rows do not evaluate it.

**Definition 1.20 (Licensed compressed trial points).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.TrialPoint`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.TrialPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A trial point has natural ghost offset N, candidate j, report prefix H, next report a and remaining reports tail. The installed offset start+j equals N, N is at most the stationary epoch tau, and j is within its installed range. The bounded trial is exactly H followed by a and tail. The prefix H belongs to the complete source traversal, its full pending frontier is a.address followed by rightsPending(a.address), and its branch and leaf counts and the current depth are less than h. The control is exactly atPrefix(j,H,a.address,mu), with mu either VALUE or the prescribed queryMode. These objects describe a mathematical relation and are not stored fields.

**Definition 1.21 (Predicates along actual executions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.RefinedRun`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.RefinedRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This finite execution relation has the same actual Read and Update steps as Run and additionally retains a mathematical predicate I at every configuration and epoch. Erasing these predicates gives a Run. If it ends at a Halt instruction, determinism ensures that every other finite Run from the same entry ends at a point satisfying I.

**Theorem 1.22 (Actual one-Update alignment).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.native_one_update_alignment`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.native_one_update_alignment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural h,T,t and every source u with length(u)=h and t at most T, put B=alignmentBudget(h,T) and U=B-t-rightClock(u). Then U is positive, t+U=B-rightClock(u), and B-2h+1 is at most t+U at most B. The difference (t+U)-(B-2h+1) is at most 2h-1. There is an actual Run of controlProgram(activeParameters(h,T)), starting from canonical POLL at epoch zero on the entry source substitution iterated t times on u, reaching fresh candidate zero at epoch U. Each absent poll is followed by precisely one Update; the observer stores no poll count or absolute epoch. This alignment statement does not require parity of h or positivity of T.

The source right clock is at most 2h-1. Its entry value is rightClock(u)+t, strictly below B. One genuine update increments it by one. Induction on the remaining difference to B builds the actual POLL, UPDATE, POLL execution, and the final poll is alpha. Only the fixed literal depth and short trial index range occur in the installed controls.

**Theorem 1.23 (Stationary bounded rows reach the original parity).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.native_stationary_bounded_execution`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.native_stationary_bounded_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix parameters P, a natural epoch tau and sources u,y with length(u)=P.h and y equal to substitution iterated tau times on u. Assume P.start is at most tau, tau is at most P.start+P.last, and either P.h is even or tau is zero. For any observation field obs and epoch e whose replies at e are exactly readout on y, the independently defined controlProgram(P) has an actual Run from fresh(0) at e to the canonical original-parity Halt at e. That canonical control has a Halt instruction. Every actual Run from the same initial control and epoch which ends at a Halt instruction has this same final control and epoch. Every finite actual Run from that entry ends at epoch e, either at this final control or at a TrialPoint with its exact proper prefix, compressed frontier, bounded counters and licensed offset. The original parity bit is true exactly when the beta-leaf count of u is odd.

**Definition 1.24 (Constants for all three regimes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.rowParameters`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.rowParameters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If active is true and T is positive, use activeParameters(h,T). Otherwise install size h, starting offset zero, last candidate T, polling depth zero and inactive mode. In particular T=0 always uses the direct traversal.

**Definition 1.25 (Common entry control).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.rowInitial`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.rowInitial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For active mode and positive T, enter canonical POLL. For every other regime, enter fresh candidate zero. The entry is independent of the source and its historical epoch.

**Definition 1.26 (Actual Update count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.rowUpdates`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.rowUpdates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For active mode and positive T, the number of genuine Updates on entry source substitution iterated t times on u is alignmentBudget(h,T)-t-rightClock(u). In the other regimes it is zero. This source-dependent number is mathematical comparison data, not stored control.

**Definition 1.27 (Actual intermediate configurations).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.RowPoint`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.RowPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At source epoch a, a is at most the terminal Update count U. Either the installed parameters are active and the control is canonical POLL or UPDATE, or a equals U and the control is the canonical original-parity Halt or a TrialPoint in the stationary image at historical epoch tau.

**Theorem 1.28 (Uniform actual bounded execution).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.native_bounded_rows_execution`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.native_bounded_rows_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural h,T,t and sources u with length(u)=h and t at most T, assume T=0 or h is even and choose either Boolean active setting. Let P=rowParameters(h,T,active), U=rowUpdates(h,T,t,u,active) and tau=t+U. Then P.start is at most tau at most P.start+P.last. Either U is zero, or it is positive and tau equals alignmentBudget(h,T)-rightClock(u). On the actual entry source substitution iterated t times on u, controlProgram(P) has a concrete Run from rowInitial(T,active) at source epoch zero to the canonical original-parity Halt at U. This is a Halt instruction, and every actual halt-ended Run from that entry has that same final control and source epoch. Every actual finite Run from the entry ends at a RowPoint(P,tau,u,U), so all trial points are stationary, licensed, and retain the exact compressed frontier and prefix counts.

For two successive reports, the full frontier identities force the next path: a branch appends a left edge, and a leaf follows nextPath. Counts and parity agree with the extended prefix. A last branch is precisely a rejected trial and increments the candidate; a last leaf is precisely a complete traversal and satisfies the exact final leaf and branch tests. Licensed decoder replies turn these structural transitions into actual GUARD and VALUE Reads. Induction through each report list and backwards through the finite interval to its first complete candidate builds the concrete Run. The existing image theorem supplies each candidate before any decoder invocation, and the full-source parity theorem identifies its output. Determinism identifies every halt-ended Run.

The path correspondence and stationary execution statements do not specify a bit-field representation or a physical installed execution. Those require additional operational statements.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.ActualCursorPrefix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.Control`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.CursorRun`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.Mode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.Parameters`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.RefinedRun`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.RowPoint`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.TrialPoint`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.Valid`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.activeParameters`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.alignmentBudget`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.atPrefix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.canonical`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.controlProgram`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.cursorStep`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.fresh`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.native_bounded_rows_execution`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.native_one_update_alignment`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.native_stationary_bounded_execution`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.nextPath`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.pending`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.queryMode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.reachable_compressed_frontier_and_trial_simulation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.rightsPending`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.rowInitial`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.rowParameters`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.rowUpdates`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.virtualDelta`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial](../BoundedPreorderTrial.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativePollingAlignment](../NativePollingAlignment.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport](../../../../ObserverMemory/Algorithms/NativeExecutionTransport.md)
