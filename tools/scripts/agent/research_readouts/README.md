# Research prediction readings

This is the input contract for `readouts.py`, subordinate to `CLAUDE.md` and the existing specification. It computes readings for `skills/autonomous-research/SKILL.md`; it does not judge mathematics, proof shape, admission or research value. Existing §3.2 evaluation and mathematical settlement supply the evidence. No value function f is registered by this contract, and no expected value or ordering is computed.

## Carrier and acquisition

One unit is one existing preregistration issue in `the-omega-institute/trureturing`. Before substantive execution, append one **unchanged issue comment** containing a fenced `research-prereg-v1` JSON block. Its GitHub REST `created_at` is the registration time of every prediction in that block. The program requires `updated_at == created_at`. The timestamp is obtained from GitHub metadata, never a payload field that would need an edit after creation. Do not put the block in the issue body: an issue's `updated_at` also reflects activity unrelated to body edits.

Append an unchanged comment containing one fenced `research-terminal-v1` JSON block to report the current settlement or obstacle. A batch has at most one block of each kind per issue, across the issue body and all comments. To revise an event, threshold or predictions, preregister a fresh unit before execution; do not replace the old blocks. Seat independence and the fidelity of the source judgment remain obligations of the owning research workflow.

Read live carriers and cited evidence with:

```sh
make -s -C tools research-readouts ISSUES="123 456" AS_OF="<UTC cutoff>"
```

`ISSUES` lists existing issue numbers; `AS_OF` is required. The command uses read-only `gh api` requests for issue bodies, **all comment pages** (`--paginate --slurp`), and cited issue/PR bodies or issue comments. Citation URLs must resolve to their own returned `html_url`. Network, permission and pagination-shape failures are named failures, never empty queues.

For offline replay, omit `ISSUES` and provide a JSON snapshot on stdin:

```sh
make -s -C tools research-readouts AS_OF="<UTC cutoff>" < /external/path/snapshots.json
```

The snapshot has exactly `issues` and `evidence`. `issues` is an array of objects with exactly `issue` (the REST issue object) and `comments` (the complete flattened REST comment array). `evidence` is an array of cited REST issue/PR/comment objects not already included in `issues`. Raw REST objects retain at least `html_url`, `body`, `created_at`, `updated_at`; extra API members are ignored. Conflicting copies of the same source and duplicate unit identities fail. Snapshots are supplied evidence: offline mode cannot authenticate GitHub metadata or detect omitted comments. Acquire complete snapshots from GitHub for attributable readings. Do not commit snapshots or aggregates to the main repository.

## Preregistration block

Use a code fence whose opening line is exactly `` ```research-prereg-v1 ``. Its JSON object has exactly these fields:

| Field | Contract |
| --- | --- |
| `event` | Object with exactly nonempty `statement` and `quantifiers` strings. The binary event is the truth of this fully quantified statement, under its stated assumptions. |
| `deadline` | UTC cutoff, strictly after the carrier's creation time. |
| `scoring_rule` | Exactly `{"name":"binary-brier","version":1}`. Version is an integer. |
| `surprise_threshold` | Finite JSON number in [0,1], chosen for this preregistration. There is no tool default. |
| `predictions` | Array of independent-seat predictions; `[]` explicitly records that predictions were not obtained. |

Each prediction has exactly:

| Field | Contract |
| --- | --- |
| `seat` | Nonempty unique seat identity in this unit. |
| `model_family` | Nonempty attributable model-family label; the output preserves actual diversity, without assuming different seats imply different families. |
| `event` | Exactly the same statement and quantifiers as the unit's event. |
| `probability` | Finite JSON number in [0,1] predicting that the event is true. Booleans, strings, null, NaN, infinity and out-of-range numbers fail. No clamp or coercion. |

All timestamps use UTC `YYYY-MM-DDTHH:MM:SSZ`. JSON duplicate keys, unknown or missing block fields, unsupported versions and malformed research fences fail. Event matching is exact text equality, not an equivalence proof. The owning evaluator must check the quantified statement's fidelity; a matching label alone is insufficient.

## Terminal block and evidence

Use a code fence whose opening line is exactly `` ```research-terminal-v1 ``. Its JSON object has exactly:

| Field | Contract |
| --- | --- |
| `event` | Exactly the preregistered statement and quantifiers. |
| `execution_started_at` | Recorded substantive execution start. It must be at or after registration, before the deadline, and no later than terminal publication. Registration later than this start fails `POSTHOC_PREDICTION`. |
| `status` | `proved`, `refuted`, `invalid` or `unresolved`, taken from the owning route's current evidence. Only proved/refuted supply a binary answer. |
| `settled_at` | Recorded mathematical settlement time for proved/refuted; null for invalid/unresolved attempts. It must lie between execution start and terminal publication. |
| `evidence` | Reference to existing settlement or obstacle evidence, with exactly `url` and a nonempty verbatim `excerpt`. |
| `shape_evidence` | Reference with exactly `url` and `excerpt`, or null when no settled §3.2 judgment was obtained. A supplied excerpt must be exactly `proof_shape: content` or `proof_shape: bind-only` from the unit's existing live-path evaluation. Invalid/unresolved attempts require null. |

References resolve to this repository's issue/PR bodies or issue comments. Each excerpt must occur in the resolved source body. `shape_evidence` reads x=1 for the existing content judgment and x=0 for bind-only. A missing judgment leaves x unmeasured for a settled answer. The program verifies reference identity and excerpt presence; it does not certify that the cited evaluator correctly assessed the live proof path or that the settlement proves/refutes the exact event. Apply the existing independent evaluation, Lean and admission requirements before supplying those judgments. The recorded execution/settlement times are workflow assertions, not independently observed process telemetry.

A scored settlement must occur **by the registered deadline**, according to its recorded `settled_at` and cited existing evidence. The reporting comment may be published later: reporting time is distinct from mathematical settlement time and from preregistration time. A late report cannot supply a late prediction, alter the registered event or replace missing settlement evidence; the owning evaluator checks the recorded settlement time against that evidence. The `AS_OF` snapshot must reach every included carrier's `updated_at`; future or incoherent metadata fails. An already settled answer can be scored before its deadline. An unresolved unit requires `AS_OF` to reach its deadline before claiming z=1; otherwise the batch fails `BEFORE_DEADLINE`. An absent terminal, invalid attempt or late settlement leaves the mathematical answer unresolved at the cutoff. It supplies no negative answer and no Brier score.

Missing whole preregistrations (historical issues) and explicit empty prediction arrays yield named unscorable readings. They never create y or a mode, and no historical probability is filled in. Without a preregistration, `evidence_status` is `missing-preregistration`: a terminal cannot be matched to a registered event. Missing mandatory fields in a present block fail the batch. A missing terminal after the deadline has structural z=1; it does not assert why research was unfinished.

## Deterministic output

The command writes a single JSON object to stdout, without persistent state or a cache. Invalid input exits 2 with `READOUT <named failure>` on stderr and **no partial stdout**. The canonical test command is `make -C tools research-readouts-test`; the same tests also run within the existing `tests-instruction-contract` CI unit.

Probabilities and scores are computed as exact rational numbers from JSON decimals. Output rationals are reduced strings (`"0"`, `"1"`, `"1/16"`); no floating-point rounding occurs. Units and seats are sorted by their identities. For a settled binary answer a, each seat's binary Brier loss is `(p-a)^2` (version 1, without the two-category factor of two). The aggregate prediction is the equally weighted arithmetic mean of seat probabilities. `surprise` is the **mean of seat Brier losses**, not the Brier loss of the aggregate prediction. y=1 iff this mean is at least the registered threshold. Proper scoring measures prediction error; neither the score nor its threshold measures mathematical information or research value. No family weighting or calibration claim is made.

Each unit reports its issue, event, metadata-derived registration time, seat/family scores, aggregate probability, surprise, x/y/z, mode, score status and evidence status. A settled unit without predictions has y=null and mode=null. With predictions but no timely answer, z=1 and x=y=0 are **structural zeros** required by xz=yz=0; scores stay empty and surprise stays null. They are not observations that the answer was expected. With predictions and an answer but no shape judgment, scoring proceeds, x and mode stay null. Illegal nonbinary coordinates or nonzero xz/yz are rejected by the classifier; supplied x/y/z fields are not accepted as substitutes for evidence.

The five modes are:

| Mode | (x,y,z) |
| --- | --- |
| `p0` | (0,0,0) |
| `p2` | (1,0,0) |
| `p5` | (0,1,0) |
| `p25` | (1,1,0) |
| `p3` | (0,0,1) |

The batch always reports all five `five_counts`, total units, scored units, `mode_denominator`, `score_coverage`, `mode_coverage` and `missing_counts`. Counts of prediction, answer, shape and mode missingness can overlap. `score_coverage` is scored units / all units; unresolved and missing-prediction units are excluded from answer scoring. `mode_denominator` includes only complete modes; X=(p2+p25)/denominator, Y=(p5+p25)/denominator and Z=p3/denominator describe that subset, not the excluded units. Zero denominators produce null rates, never invented zeros. Complete five-cell counts are retained even when X/Y/Z coincide: the count difference (1,−1,−1,1,0) preserves these rates but changes the joint distribution. No f, E[f], ranking, residual-sufficiency judgment, quota or admission decision is produced.
