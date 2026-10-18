# Bounded autonomous research wake

This entry implements the mechanical execution boundary of `skills/autonomous-research/SKILL.md`. `CLAUDE.md` and the specification retain authority. The host supplies subsequent wakes; this program has no daemon, timer, scheduler or human-review state. It generates results directly rather than selecting digestion atoms.

Run `make -C tools autonomous-research-round ROUND_WAKE=<stable-host-invocation-id>`. A retry or process restart must reuse that identity. A genuinely new host wake supplies a new identity. Concurrent invocations share one nonblocking lock and one active unit in the current worktree. A new wake resumes the active unit before generating another. An already completed wake does no work. Each wake starts at most one new unit.

`make -C tools autonomous-research-round ROUND_MODE=dry-run` uses local seats/carriers and actually invokes the existing `research-readouts` make entry on its synthetic REST snapshot. It publishes no research and claims no Lean verification or novelty. `make -C tools autonomous-research-probe` makes one real Claude prediction capability call, reports the carrier's `modelUsage` model identity and parsed response, and publishes nothing. Probe calls are not registered research predictions or pilot units; do not include them in L2 scores.

## Route and contracts

| Phase | Owner / executable boundary |
| --- | --- |
| Generate | `python3 tools/scripts/agent/nyx/nyx.py ask`; full theorem/construction, assumptions, proof, proposed P/I witnesses and Application draft; no Lean capability is assumed of the generator. |
| Candidate carrier | A normal issue containing result exposition and a stable action marker; the event is retained unchanged in the active unit. |
| Isolated forecasts | Fresh `codex exec < promptfile` and Claude CLI processes receive only the quantified event. Claude has no tools, MCP servers or persistent session. The requested codex model and Claude's carrier-returned model determine attribution; seats are not counted as different families by name. |
| Preregister | An unchanged comment with exactly the existing `research-prereg-v1` fields. The original REST creation timestamp is the commitment time. Complete issue/comments are checked again before execution. |
| Solve | A fresh workspace-write codex process uses the current formalization skill and existing make doors; it returns actual D5/Reg modules or a named unresolved obstacle. It cannot change the event or publish results. |
| Check | The controller executes `make lean-report-scoped LEAN_TARGETS=...` and `make gate BASE=<pinned-head>`; neither a worker assertion nor a partial check substitutes for exit 0. |
| Evaluate | A separate read-only codex process evaluates the exact event, fidelity, §3.2 live proof shape, admission and §3.3 use. Oracle and Claude never validate. |
| Settle | Normal result/evidence and successor exposition in an issue comment; an unchanged `research-terminal-v1` comment cites it. No additional fields enter either strict block. |
| Read and hand off | `make -C tools research-readouts ISSUES=... AS_OF=...`. Unresolved units wait for the registered cutoff without sleeping. The next unit receives the predecessor issue, whose result contains the successor statement. |

The controller does not publish PRs, merge, change the harness during research, consume a candidate database, or compute an information score. Normal content admission, actual Application/FIB evidence and downstream delivery remain necessary. A local mathematical settlement is not a research-hit or remote-CI claim. The compiled report retains its existing custody consumer; this entry does not introduce a standalone `fib_analysis` trust path.

## Durable bounds and recovery

The fixed limits are 300 seconds per seat (below the 1200-second ceiling), 3600 seconds and ten seat calls per unit, and 3600 seconds and ten seat calls per wake. The bounded pilot allocation is six distinct wake identities and sixty seat calls. A call means one carrier invocation, including failed attempts; provider-internal turns are not independently observable here. Checks receive at most the remaining mathematical allocation, with a 900-second check allocation. Administrative reads/writes reserve at most thirty seconds each; HEAD reads reserve five. An interrupted required check supplies no successful verification.

Reservations and an inflight marker are fsynced before spawning. Allocations are never refunded, including on spawn failure or early completion. Limits, mathematical deadline, event, forecasts, registration timestamp and execution start cannot be widened or rewritten on restart. A new wake cannot reset an active unit's mathematical budget/deadline. Completed units are not solved again. Seats run serially (at most one child seat and one oracle); codex delegation is disabled. A bounded per-call supervisor holds the same lock and kills its process group at the reserved deadline even if the controller dies. It neither starts research nor schedules another wake.

After the old supervisor releases the lock, a recorded `CALL_OUTCOME_UNKNOWN` never launches a replacement seat: a lost forecast is missing, a lost generation is an invalid unregistered attempt, and a lost solver/check/evaluator result becomes unresolved. Outcome and phase are saved together. Restart removes orphaned temporary streams under the lock. External-write uncertainty follows the stricter reconciliation rule below and is never converted into permission to resend.

Mathematical budget/deadline exhaustion closes an executed attempt as unresolved, using the remaining administrative allocation. An unexecuted attempt records the resource boundary without fabricating an execution start or strict terminal block. If it was preregistered, L2 reads its missing terminal only at the original cutoff. A wake whose administrative allocation is exhausted leaves that closure for a subsequent host wake. A fresh unit is possible only after the previous unit ends, within the unchanged pilot allocation.

The ignored `.lake/autonomous-research-round/checkpoint.json` holds only the active unit/phase, necessary carrier commitments, consumed allocations, bounded wake identities and a pending write intent. Temporary prompts, raw streams and schemas are removed on normal carrier exit or locked restart cleanup. No checkpoint, snapshot, aggregate, transcript or experiment is committed. Deleting a checkpoint is not a restart mechanism.

Each issue/comment write has an action identity derived from unit, purpose and exact body digest. Its intent is saved before the API request. Before a write, the controller reads every page of the relevant REST carrier collection; candidate discovery includes open/closed issues updated since the fixed intent timestamp, not the search index. It accepts only one exact marker/body/metadata match. A lost receipt is reconciled on reentry; zero or conflicting matches after an attempted write suspend without resending. Source edits, duplicate commitments, terminal blocks before execution and changed HEAD stop the unit. There is no automatic edit of previous blocks.

## Tests and ownership

`make -C tools autonomous-research-round-test` runs Python behavior tests against the production state machine, subprocess timeout primitive, transport construction, strict-block parser and local make rehearsal. `ResearchReadoutsScriptTests` invokes it in the existing `tests-workflow-script` CI unit. `Meta/ci-units.json` explicitly selects that unit for this directory. No workflow, required-check name, judge rule or admission state is added.

| Element | Requirement served; why the existing mechanism is insufficient |
| --- | --- |
| `controller.py` | U2 phase recovery, fixed commitments, single active unit, precharged budgets and exact write reconciliation; existing callers performed these steps manually and L2 is stateless. |
| `runtime.py` | U2 durable atomic checkpoint, lock and bounded process supervisor surviving controller death; existing readout arithmetic owns none of these lifecycle invariants. |
| `backend.py` | U2 canonical gh/make calls, full carrier acquisition and preregistration recheck; no replacement parser, gate or proof judge is introduced. |
| `workers.py` | U2 isolated role calls and schemas; U4 attributable Claude inference; existing codex/oracle doors execute individual calls without this phase contract. |
| `entry.py` / make doors | U2 one bounded host wake, local rehearsal and capability probe; existing make entries do not execute an entire unit. |
| `rehearsal.py` / `test_round.py` / CI bridge and whitelist | U2 fault-injection and production-chain execution; L2 tests cover arithmetic, not controller crashes, budgets or ambiguous writes. |
| This contract | U2 invocation, stop meanings and evidence limits for the host; the research skill does not specify this executable's durable storage or command interface. |

Named stops include `ALREADY_RUNNING`, `HEAD_CHANGED`, `WORKER_TIMEOUT`, `WORKER_MALFORMED`, `CALL_OUTCOME_UNKNOWN`, `WRITE_UNKNOWN`, `WRITE_AMBIGUOUS`, `CARRIER_CONFLICT`, budget/deadline boundaries and `WAIT_DEADLINE`. Prediction capability failures are disclosed and do not fabricate a probability or family. Solver/check/evaluator failures cannot become proved/refuted answers; they retain an unresolved boundary. Fault tests specify the expected stop or terminal outcome in their assertions.
