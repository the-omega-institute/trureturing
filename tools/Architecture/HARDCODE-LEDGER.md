# Hard-code guard and residual ledger

> **Maintenance contract:** every newly discovered hard-code family must update this
> ledger in the same change. If a low-false-positive predicate exists, fix the stock,
> add the guard, add an executable rejecting fixture, and update the matrix. Otherwise
> add or refine an `HC-OPEN-*` entry with concrete examples and the reason it cannot be
> judged honestly. A green repository is never, by itself, a proof of "no hard-coding."

Audit baseline: `origin/dev` at `4f2d166` (PR #95, theory-zero), audited on
2026-07-14 from `harness/hardcode-audit`.

## Answer

No. PR #95 removed internal theory families from the formal/program layer. The literal
scanner that later claimed to tripwire their return was retired by `46220826c`; no current
guard owns that family (`HC-OPEN-014`, `D5-T0036`). The repository still has several
strong, narrow hard-code guards; it does not have, and cannot honestly claim, a general
proof that no hard-coded value remains. Literal intent, semantic duplication, encoded
values, and test-fixture structure remain partly or wholly outside those predicates.

In this ledger, "hard-code" means a value copied or embedded where another artifact
should be authoritative. A literal is not automatically a defect: mathematical
constants, protocol tags, negative fixtures, and canonical definitions are often the
right source.

## Guard matrix

`Red fixture` names an executable negative case. Counts below are fresh observations
from this audit, not substitutes for the named predicate. The matrix includes checks
that directly compare a consumer field/literal/configuration with an authority, or
reject a hand-produced projection. Orthogonal SL rules for imports, proof closure,
capacity, append-only history, protected semantics, anomaly balance, axioms, future
theories, and bootstrap admission are outside this anti-hard-code inventory.

| Check | Machine criterion and scope | Red fixture evidence | Covered family |
|---|---|---|---|
| FILEMAP custody and producer policy | `Meta/FILEMAP.toml` is parsed fail-closed; every tracked/unignored path matches exactly one pattern, registry root files equal tracked root files, generated files match the producer inventory and name that producer, data names an existing program verifier, and class directories remain pure. Residence policy states the no-data-under-`tools/` ideal and now freezes the closed zero-violation state. | Yes: unclassified, ambiguous, registry drift, missing loader, missing/mismatched producer, missing generated `produced_by`, directory mixing, unmarked protected-surface data, exact residence inventory drift, data-to-generated reference, and Lean-to-generated import red fixtures. | Hand-maintained or implicit file ownership, generated outputs without an executable producer, and unmarked or newly added protected-surface data. The bounded dependency predicate remains recorded under `HC-OPEN-012`; `RESIDENCE-EPOCH` is closed. |
| Values constant-set ownership | Engine validates canonical v2 projection schema, status/receipt shape, input attestation, unique sorted IDs, and complete Lean provenance without owning the ID set or kernel names. Scribe loads a non-empty, unique, sorted catalog of any size from `values-kernels.toml`; canonical re-emission is byte-exact. | Yes: the two-item projection, synthetic future-kernel, and one-row TOML fixtures each failed against the former C# copies before repair. Production writer byte-stability and current catalog-content tests remain authoritative for today's 14 rows. | Constant identity/cardinality and computation selection copied from the emitter data into the Engine or loader. It does not make arbitrary projections canonical: the canonical writer binds output to TOML/Lean at production time. |
| BannedApi culture matrix | The official semantic analyzer consumes an exact, duplicate-free 143-member culture-sensitive denylist in Engine, Scribe, and CLI; `selftest` checks project wiring, the central version, actual lock framework keys, lock attachment, and the exact matrix (`SelfTestGovernancePolicy.cs`). | Yes: synthetic missing-analyzer and `net99.0` lock fixtures in `SelfTestGovernancePolicyTests`, plus the retained compile-fail proof. Attaching it to CLI made providerless `int.TryParse` fail with the sole RS0030 before repair. | Providerless numeric/temporal parse, try-parse, and formatting overloads in production projects. |
| BannedApi nondeterminism matrix | Engine, Scribe, and CLI consume the exact 7-member ambient clock/entropy/tick denylist. Engine and Scribe also consume the one-member GUID denylist; CLI is outside that GUID predicate because it allocates ephemeral workspaces. `selftest` checks the exact three-file matrix (`SelfTestGovernancePolicy.cs`). | Yes: exact-matrix synthetic fixtures plus the retained compile-fail proof, whose complete run produced exactly 18/18 RS0030 diagnostics. | Ambient runtime nondeterminism in all production projects; GUID creation in deterministic Engine/Scribe code. It does not prove every future CLI GUID use is ephemeral. |
| SL-004 Mirror completeness | `mirror-B` and `mirror-E` header fields, when not `none`, must have the matching `D5/B/` or `D5/E/` address family and resolve to an existing projection (`RepositoryRules.Structure.cs:98`). | Yes: active-rule `mirror` mutation passed by deleting the referenced Blueprint. | Hand-copied formal-to-projection addresses; it checks existence and address family, not content equality. |
| SL-006 Generated status | In `D5/`, Blueprint, Evidence, Library, Papers, and Chronicle, regex-recognized handwritten English/Chinese status badges are rejected (`RepositoryRules.Structure.cs:123`). | Yes: active-rule `badge` mutation passed. | Handwritten lifecycle/status claims in recognized forms. |
| SL-011 Controlled domains | D5 formal and Blueprint/Evidence stratum paths must use a registered domain at its registered stratum (`RepositoryRules.Structure.cs:208`). | Yes: active-rule `domain` mutation passed. | Directory/domain vocabulary copied outside `Meta/domains.yaml`. |
| SL-012 Six-line Lean header | Every D5 Lean file must start with the exact six-line machine header; a unique parseable header GID must equal the path-derived GID (`RepositoryRules.Structure.cs:257`). | Yes: active-rule `header` mutation and the `missing-six-line-header` golden case passed. | Hand-copied or missing formal GID/header metadata. Duplicate GIDs are separately rejected by SL-015. |
| SL-013 Permanent task ledger | The descriptor remains at its positional slot but is deferred `NoFindings`; it does not enforce task prose. `TASK D5-Tnnnn` remains the case-address vocabulary consumed by SL-016 and SL-019. | Deferred under D5-T0013; no active SL-013 rejection predicate exists. | Task-code references used by active consumers, not the shape or append-only status of free-form task prose. |
| SL-015 Machine fields and GID grammar | Repository path policy, GID character set, duplicate GIDs, evidence-kind collisions, anchor syntax, and JSON formula grammar are checked (`RepositoryRules.Content.cs:11`). | Yes: active-rule `formula` mutation plus golden cases for duplicate/unsafe GIDs and evidence collisions passed. | Canonical address/field literals and the closed formula language, not arbitrary constants. |
| SL-016 Digestion ledger | `Meta/Digestion/backfill/` is loaded fail-closed; source uniqueness, boundaries, fingerprints, receipts, CAS integrity, and derived migration/truth status are recomputed by `tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs`. TASK case-to-module mappings are derived from all `D5/**/*.lean` inputs; cross-module duplicate cases remain an independently meaningful ambiguity error. The loader still contains a legacy single-file dual-read path, but no legacy file is indexed; `D5-T0035` owns the pending ruling on that compatibility path; this ledger does not decide whether it stays. | Yes: the active-rule `backfill` mutation and directory-ledger fixtures in `tools/tests/StrataLint.Tests/Rules/RuleEngineTests.cs` reject malformed ledger data and missing or corrupt CAS blobs while admitting a valid directory ledger; loader tests reject ambiguous derived TASK mappings. | Theory-source provenance and handwritten digestion state after theory-zero. |
| SL-017 Typed anchor membership | Formal header anchors and library query targets must be canonical catalog members or valid local targets; missing/noncanonical catalog bytes fail closed (`RepositoryRules.Content.cs:194`). | Yes: unregistered literature, malformed external, and uncataloged opaque anchor fixtures. | Invented or unregistered formal references. |
| SL-018 Machine-produced values | Only `Evidence/D5/values.json` is accepted as the canonical projection address (`RepositoryRules.Content.cs`). The rule no longer re-derives the projection's own bytes from a recomputed producer attestation: that was guarding a projection, and CLAUDE.md section 0 makes the governed producer plus its declared input closure the authority instead. | Yes: the active-rule `values` mutation fixture, plus a green fixture proving mutated canonical bytes are admitted. | Values written to a noncanonical `Evidence/D5/values.*` address. It no longer detects hand-edited bytes inside the canonical projection; `make emit` re-derives them from `Golden/values-kernels.toml`. |
| SL-014 Toolchain upgrade compatibility | Deferred under `D5-T0010`; `tools/StrataLint.Engine/Rules/RepositoryRules.cs` registers a deferred case with no rejection predicate. | No active red fixture; the deferred-state test passed. | **No active broad or narrow toolchain/version copy guard.** `HC-OPEN-005` records the retired narrow scanners; the BannedApi analyzer lock check above remains independently active. |

## Executed evidence

- CanonicalSources and TheoryIsolation selection: 31/31 tests passed.
- Golden corpus storage and closed-stratum anchor selection: 7/7 tests passed.
- BannedApi configuration/coverage selection before this audit's additions: 7/7 passed.
- Active SL red/green selection: 20/20 passed, including
  SL-004/006/011/012/013/015/018.
- Focused SL-016 theory-zero selection: 7/7 passed.
- New guard red run: four stock failures, exactly CLI attachment, mixed denylist,
  two copied SDK pins, and copied package version.
- New guard green run: 18/18 passed.
- Guard fail-closed additions: empty central catalog 4/4, required SDK references 4/4,
  and framework-agnostic lock lookup 1/1 passed after their observed red runs.
- CLI ambient-runtime attachment red/green: the missing attachment failed first;
  split 7-member ambient plus 1-member GUID configuration then passed 17/17, and the
  compile-fail proof remained exactly 18/18.
- SDK scope/case red/green: disabling mixed-case action identity and `.yaml` discovery
  made exactly the two corresponding fixtures fail; restoring both made 2/2 pass.
- BannedApi compile-fail proof after denylist split: build exit 1 by design; all 18
  marked lines produced RS0030, no marked line escaped, and no other error appeared.
- Atomizer/specification canonical-source selection: 15/15 focused cases passed after
  the specification-copy stock fixture was replaced with neutral synthetic text.
- Target-framework guard selection: 5/5 cases passed; explicit harness-path and shared
  gate contract selection: 11/11 cases passed, including the out-of-root rejection.
- Values authority selection: Engine schema/attestation loader 9/9 and Scribe catalog,
  writer, and byte-exact projection selection 8/8 passed.
- Definitions retirement migration autopsy: moving the canonical TOML writer into CLI
  activated the existing BannedApi analyzer on that source; the first Debug build failed
  with exactly one RS0030 at providerless `int.ToString("X4")`. Supplying
  `CultureInfo.InvariantCulture` repaired the deterministic writer, after which the Debug
  solution build passed with zero warnings and errors.
- Definitions retirement repository-scan autopsy: the first full Architecture run found
  16 existing-file literals that focused selections had missed (14 in the new retirement
  ownership test and two in the target-framework fixture). Each contract path was promoted
  to a named `const string`; the policy stayed unchanged, its failing selection passed 1/1,
  and the Architecture suite excluding the pending C0 renewal passed 101/101.
- Ceremony setup autopsy: the first report attempt assumed a nonexistent
  `~/.elan/bin/lake`; resolving the executable produced both reports. The first verifier
  attempt then used the candidate six-argument contract against the base four-argument
  CLI and failed closed. Obeying the base protocol exposed the substantive v1 codec limit:
  removing the Definitions exemption made candidate-only SL-022 diagnostics malformed to
  the predecessor. The exemption was restored; directory absence remains machine-guarded.
- FILEMAP standard action: stock data under `Meta/StrataLint/Golden` was moved to top-level
  `Golden/`; the first verifier audit found that `StrictTextLoader` named no implementation.
  A focused repository-conformance run failed with exactly two `FILEMAP-DATA-VERIFIER`
  findings, after which both text-data classes were bound to the real strict-UTF8
  `SnapshotDecoder`. FILEMAP manifest, architecture, and emitter selections cover the
  closed-world, red fixtures, and byte-exact dependency projection.
- Spec-digestion migration autopsy: the first base-controlled replay failed closed in
  `DigestionFingerprint` because the A8/A18/6.2 edits shifted all twelve spec acceptance
  slices by 1,035 bytes. The old registered slices were found exactly once in the current
  spec with unchanged bytes and fingerprints; `Meta/BACKFILL.yaml` moved their contiguous
  boundaries from `26902..30633` to `27937..31668`. The next base and candidate checks
  passed that boundary instead of throwing a UTF-8 decoder exception.
- Ceremony hash-tool autopsy: macOS Perl `shasum` rejected the process `C.UTF-8` locale
  before reading either report. The system OpenSSL SHA-256 implementation then measured
  both independently generated Lean reports as
  `797dae7a5a1177d47acb9e7affc20fc84762dc7f856bcbdfc4296b70ba30e26d`, and `cmp`
  confirmed byte identity.
- Frozen-ledger relocation autopsy: the first candidate admission rejected the deliberate
  `Meta/StrataLint/Golden/Frozen/events.jsonl` to `Golden/Frozen/events.jsonl` move because
  SL-008 equated frozen identity with one physical path. Both Git entries had the same
  blob OID `92263724b1738f4852ee964cb822ec140ae09c5c`. Baseline resolution now permits only one
  byte-exact prior `*/Frozen/events.jsonl` source when the canonical baseline path is
  absent; changed and ambiguous sources remain rejected by focused fixtures. The next
  candidate admission reached the expected SL-022 boundary with no SL-008 finding.
- Historical Scribe replay autopsy: the next conservative run reached the candidate
  harness but tried to verify the baseline tree with the candidate's expanded
  `DocumentDefinitions`; six producer sources correctly did not exist in the old tree,
  so replay failed as infrastructure before comparing dispositions. Baseline-tree replay
  now derives the frozen candidate change set and applies the same rule as production
  admission: an emitter mismatch may yield no Scribe capability only when SL-022 already
  classifies the change as protected. A clear content change still throws, as the paired
  red/green fixture proves.
- Historical values replay autopsy: after Scribe replay was restored, the candidate
  harness flipped the admitted baseline tree to SL-018 because its v2 input manifest
  named the former kernel-data residence. Production still accepts only
  `Golden/values-kernels.toml`; conservative baseline replay can supply a historical path
  only after finding exactly one prior `*/values-kernels.toml` whose bytes equal the
  candidate canonical file. The loader then verifies the old manifest's declared path,
  individual SHA-256, and combined input SHA-256 without an implicit legacy alias.
- Historical frozen-ledger replay autopsy: restoring the values attestation exposed the
  same old-tree/current-path distinction in SL-008. Candidate admission already resolved
  an old baseline ledger against a new canonical current ledger, but replay evaluates the
  old tree as both sides. The validator now accepts an explicit replay path selected by
  the shared canonical-or-unique-byte-exact resolver; production still defaults to
  `Golden/Frozen/events.jsonl`, and changed or ambiguous historical sources fail closed.
- Predecessor gate boundary autopsy: after all historical identities were restored, direct
  base-owned replay preserved 31/31 baseline admits and both harnesses admitted the actual
  baseline tree. The `origin/dev` verifier still rejected certification because its
  harness blocks the new top-level `Golden/**` candidate and its protection-monotonicity
  check requires six newly added `Blueprint/**/*.scribe.cs` data files to remain under
  SL-022. Satisfying those findings would reverse the approved data-residence rule. This
  migration therefore needs a staged predecessor protocol update; no green C0 certificate
  was substituted for the emitted conservative-violation evidence.
- Full-suite projection autopsy: focused FILEMAP selections missed six stale consumers and
  one repository-wide guard. The first solution run found the old Golden fixture path and
  SL-022 expectation, a five-document Scribe discovery list, two ambiguous `Program`
  reflection anchors, and sixteen existing-file literals outside named constants. The
  consumers now use canonical loader/constants or enumerate all eleven definitions; the
  repository-path literal policy was not weakened, and all corresponding focused reruns
  passed.
- Residence-epoch split autopsy: the caller meta-judge adopted the prior PARTIAL verdict:
  making the old judge accept the combined move would require weakening the recorded
  residence or protection law. The seven Golden artifacts therefore returned by 100%
  Git rename, the values attestation returned to its prior input identity, and the
  relocation-only values/frozen replay adapters were reverted. FILEMAP remains active and
  freezes the five concrete `kind=data` violations instead of claiming zero violations.
- Residence spec-boundary rebind: A8/A18 residence wording shifted the twelve immutable
  acceptance samples by 372 bytes. Each prior byte slice matched the revised spec exactly
  once with unchanged SHA-256; only the contiguous boundaries moved from
  `27937..31668` to `28309..32040`.
- FILEMAP predecessor-registration autopsy: the first split-epoch conservative replay
  preserved all 31/31 corpus admits but the base harness blocked the actual candidate with
  SL-000 because `Meta/FILEMAP.toml` and `Generated/FILEMAP.md` were known only to
  candidate C# path exceptions. The predecessor already reads candidate registry
  `governance_documents` before its closed-world switch, so both artifacts now use that
  shared declaration and the duplicate candidate-only exceptions were removed.
- Shared-judge identity-drift autopsy: the first final gate reused the clean `dev`
  worktree at `36ce721`, then PR #105 advanced both `origin/dev` and that worktree to
  `77664ec` during conservative replay. The verifier failed closed with repository
  identity drift. This branch merged the new base without rebase; the renewed ceremony
  and final gate therefore bind the stable post-merge identity instead of reusing the
  stale certificate.
- RESIDENCE-EPOCH predecessor-bridge autopsy: exact base
  `ed50b8859574a461f67412c138e1fc4080cf162d` rejected the future P2 tree even though
  contract-plan comparison ran and accepted the exact five-path contraction: the
  certificate recorded all five `retired_exact_paths`, `uncovered_obligations=[]`, and
  eligible base-owned plans for that delta. `CustodyTransferV1` suppresses only those
  mapped SL-022 protection retirements; it cannot waive the independent actual-tree
  SL-000 from the closed `RepositoryPathPolicy`, SL-018's required
  `Meta/StrataLint/Golden/values-kernels.toml`, or the offset SL-016 block. This bridge is
  pure expansion: it moves no data, consumes no plan, changes no protection policy,
  exclusion, or C0 ceremony, and admits only the exact future files plus flat canonical
  case data. The values loader keeps the old writer input but accepts exactly one of the
  old and future residences, with the same ordered manifest and hashes; both or neither
  fail closed. P2 performs the move and contracts this temporary dual-residence domain.
- Residence P2 fixture-state autopsy: the first full non-C0 run failed 12/639 because
  synthetic contract comparisons derived their pre-P2 baseline from the now post-P2
  `Current()` policy, erasing the intended retirement delta, while GoldenRecord's
  temporary repository omitted the newly external fixture registry. The fixture origins
  now declare an empty-exclusion predecessor explicitly and copy every required external
  input; the exact 26-test failing selection passed before ceremony work resumed. The
  next architecture scan then caught three real paths inline in the new missing-registry
  fixture; each was promoted to a named test constant without weakening the path policy.
- Residence P2 C0 replay autopsy: base `3119316` evaluated preimage `5fae3a2`; the actual
  candidate was blocked by SL-016 and SL-022, the actual baseline flipped to SL-018, and
  the finite replay preserved 37 base admits but only 36 candidate admits. Contract
  accounting still recorded all five retired exact paths with `uncovered_obligations=[]`.
  The roots were twelve stale spec-acceptance boundaries after the P2 spec edit and the
  baseline values attestation naming its former kernel-data residence. The first canonical
  `make ingest BASE=origin/dev` also failed closed because CAS-backed `atomizer:none`
  boundaries were returned unchanged; ingest now requires each trusted CAS blob to have
  one byte-exact source match and rejects missing, changed, or ambiguous matches. Its
  successful rerun changed only the twelve start/end pairs. Production remains single-home
  at `Golden/values-kernels.toml`; only conservative baseline replay can pass an explicit
  historical suffix path selected by a unique byte-exact relocation, with missing, drift,
  and ambiguity all failing closed.
- The next C0 replay restored the baseline tree and all 37/37 admits, then rejected the
  actual candidate only because the four new ingest regressions pushed
  `DigestionLedgerTests.cs` to 821 lines. The tests moved intact to a partial-class sibling;
  both files are below the SL-003 ceiling and no capacity rule was weakened.
- After that split, three exact-base replays emitted no certificate because the candidate
  worker exhausted its unchanged 180-second budget. The replay-only values resolver had
  loaded the entire candidate revision to obtain one canonical TOML blob; after the CAS
  epoch, `ReadRevision` expands that scan into a `git show` per repository file. The
  resolver now reads only the exact-commit, exact-path regular blob while actual-candidate
  admission retains its complete snapshot. The timeout was not raised or bypassed.
- The repaired replay against base `df14b4c43e001308e2991d8096f8500b8f167856`
  and preimage `a2c5f008d3169dc771c7a8ff30657ec9c1c5df42` then completed within
  the unchanged budget: zero findings, 117 golden cases, 118 total corpus cases, six
  contract attacks, 37/37 preserved admits, the exact five retirements, and no retired
  rule or uncovered obligation. Before that certificate could be installed, `origin/dev`
  advanced through PR #131; the branch merged it without rebase and discarded the stale
  certificate as a final authority rather than pinning an obsolete judge.
- Independent code-quality review then found that the exact-path Git helper checked only
  the OID's hexadecimal shape: `git ls-tree` also accepts tree and annotated-tag OIDs, so
  those object types could violate the helper's exact-commit contract. A regression first
  reproduced both false accepts; the helper now requires `git cat-file -t` to return
  `commit`, while valid commits still read one exact regular blob and missing paths remain
  closed. The review-fixed commit became a new clean ceremony preimage.
- The final C0 renewal binds exact base `88de8b8666bf3292c11f62d662c7e9e46c68385a`,
  preimage `b929bff94caead1267329d429865fa3695262156`, and tree
  `9ab505b1d0f1c2b5291ae1ee79c0de7098381d58`, with certificate SHA-256
  `b7952b9296cb240685142b60540f8bbc1b85f30ffc41cdf2801a97fc88548dbf`.
  It repeats the complete 117/118/6 and 37/37 evidence, admits the actual baseline under
  both harnesses, admits the actual candidate provisionally with only SL-022 diagnostics,
  consumes both RESIDENCE plans exactly once, retires exactly the five registered paths,
  and reports `retired_rule_obligations=[]` and `uncovered_obligations=[]`.
- The first final `make gate BASE=origin/dev` attempt completed its build, 911 tests,
  selftest, both Lean reports, emission check, and content admission, then its baseline
  corpus worker exceeded the unchanged 180-second budget. Process evidence showed an
  unrelated formalization worktree running another conservative corpus worker at the
  same time; the identical review-fixed C0 had already completed without that CPU
  contention. No timeout or rule was weakened: this lane waited for the external gate to
  finish before rerunning the same command from a clean tree.
- During the final replay, `origin/dev` advanced again through PR #132. The branch merged
  exact base `f91ec8379d049c4d74bf584bef5e0533a3d1f4cb` without rebase. FILEMAP's
  conflict retained both independently added loader identities; the digestion conflict
  kept the P2-only CAS boundary helper while using dev's extracted shared test support.
  The first targeted compile then exposed that a `using static` directive is file-scoped,
  not inherited by a partial-class sibling. Adding the same support import to that sibling
  changed the exact red compile into 24/24 digestion and 17/17 FILEMAP tests.
- The renewed C0 now binds preimage `797f0f94e6c55a615d4d550e9951a874a73a23b5`,
  tree `a71d478795f91eafdab5abb8c87a3bbb83394fcf`, and certificate SHA-256
  `7d0525e55269fee993e6a3fa174a770acdacffa09b896148043dc2d0f639c6c2`.
  Both base-owned Lean reports converge at `59bfd4fd14f72b05aaaa910022e1f9388891886e90eb1f3fb3ffd16aade5c545`;
  replay again reports 117/118/6 cases, 37/37 preserved admits, zero findings, the exact
  five retirements, and empty retired-rule and uncovered-obligation sets. Both harnesses
  admit the actual baseline and provisionally admit the actual candidate with only SL-022.
- The first post-ceremony `make test` then read the repository's canonical raw Lean report
  left by the pre-merge gate, while the renewed report existed only in the retained C0
  dossier. Scribe discovery rejected the three PR #132 modules missing from that stale
  input, yielding the sole failure out of 916 tests. The same base-owned producer emitted
  the canonical path at the already certified
  `59bfd4fd14f72b05aaaa910022e1f9388891886e90eb1f3fb3ffd16aade5c545`
  address; the unchanged test command then passed 916/916. No source rule or test
  expectation changed.
- After that full replay passed, `origin/dev` advanced through PR #136 with one
  `CLAUDE.md` governance anchor. The branch merged exact base
  `015d6d06d394aea2267fcd02c8a0b70a0a8c2f28` without rebase or conflict. Because C0
  binds exact repository identities, neither the preceding certificate nor its completed
  verification was reused for the final push.
- The final renewed C0 binds clean merge preimage
  `4d569d54170467094332e7cd9483dcc5bdc63e92`, tree
  `1da2c54ce459e56d21c4de3b375165f8a5bec72a`, and certificate SHA-256
  `1654c7f348da4a3a54ba35bcf7001e8dd9c0438a1cd1ceefe4bade2f086047e2`.
  Fresh reports from the base-owned producer again converge at
  `59bfd4fd14f72b05aaaa910022e1f9388891886e90eb1f3fb3ffd16aade5c545`;
  replay remains 117/118/6 and 37/37 with zero findings, the exact five retirements,
  and empty retired-rule and uncovered-obligation sets. Both harnesses admit the actual
  baseline and provisionally admit the actual candidate with only SL-022.
- Growth-1 began from an explicit evidence gap: the requested growth-audit
  `seat1-result.json`, `seat2-result.json`, and both seat logs were absent after searches
  across the accessible home tree, `/tmp`, Darwin temporary roots, Git history, agent
  traces, Spotlight, and mounted volumes. The user-supplied observations remain the
  honest evidence boundary: 11 obsolete worktrees represented 108 GiB of logical data,
  and each duplicate Lean inspection cost about 192 seconds. No replacement log or
  synthetic seat result was invented.
- The real `make clean-lanes BASE=origin/dev` dry-run classified 98 records and marked 71
  removable while changing neither the worktree inventory nor local-ref hashes. Force
  mutation ran only inside disposable Git fixtures; 9/9 focused cleanup tests covered
  merged, dirty, unmerged, current, orphan, detached, broken-pointer, gitless, symlink,
  and foreign cases. The shared repository was never subjected to an unreviewed force run.
- The first ceremony gate fetched newly merged PR #139 and correctly failed infrastructure
  admission because base `204538aac6dcb45302148dc4b59a53034dab3648` was not yet an
  ancestor of the candidate. Its pair stage still proved one 187-second inspection, a
  byte-reused baseline report, and a final failed timing summary. The branch merged that
  exact base without rebase rather than pinning the obsolete predecessor.
- The next gate reached content admission and exposed two unregistered temporary planning
  documents plus all twelve A20-shifted `atomizer: none` specification receipts. The plan
  and design remain in Git history while the sole normative contract stays in A20. The
  canonical ingest moved every unchanged sample boundary by exactly 2,080 bytes and
  changed no fingerprint, CAS ref, atom identity, or status; its repeat reported
  `ledger_changed=false`, `cas_objects_written=0`, and stable BACKFILL SHA-256
  `d2c5c909bee2656173bc3601a49519b927bd0a1b9f4ff0334afb59253a7febcf`.
- Extracting the emitted certificate first reproduced the known Darwin locale failure:
  Perl panicked before reading bytes under inherited `C.UTF-8`. Repeating the same
  byte extraction with `LC_ALL=C LANG=C` and `sed`/`jq` validated the unique certificate;
  neither gate output nor certificate bytes were changed by the failed auxiliary probe.
- The first focused C0 run passed 5/6 checks and rejected only the ceremony record shape.
  Address replacement had left the new `0e16...` and `671d...` controller blobs in their
  predecessors' positions, violating complete-record ordinal order. Moving those two
  unchanged records to their canonical positions restored the declared C0 grammar; no
  address, controller membership, corpus byte, certificate, or verification rule changed.
- The renewed Growth-1 C0 binds base
  `204538aac6dcb45302148dc4b59a53034dab3648`, clean preimage
  `5f6333ec00a95b9f78412605df6ee8e386cff97d`, tree
  `32446c45cfd7e5af296d4df1bf8334c9c9541179`, and certificate SHA-256
  `ced699912ac9872c24e7ad53d50d071756bcb30e707b4941455b387725e756ba`.
  Candidate and baseline input address `5a142073fb2a792096e57f81e4d03b90e2e459b2a89459f8c2385b71ba12c27f`
  ran the producer once and attested baseline reuse at report SHA-256
  `59bfd4fd14f72b05aaaa910022e1f9388891886e90eb1f3fb3ffd16aade5c545`.
  Replay reports 117/118/6 cases, 37/37 preserved admits, zero findings, no retired paths
  or rules, and no uncovered obligations. Both harnesses admit the actual baseline and
  provisionally admit the actual candidate with only SL-022. Machine timings were 181s
  Lean reports, 19s emission, 394s admission, and 595s total; this ceremony-only run
  explicitly recorded engineering as skipped, while final `make preflight` remains the
  acceptance owner that executes engineering once before passing that explicit skip.
- The first full preflight stopped before gate after the main test assembly passed 675/676.
  `CoverageCommandTests.TopLevelUsageNamesCoverage` still coupled coverage to the former
  immediately preceding `check` token, so inserting the registered `clean-lanes` command
  made that stale adjacency fail while the complete root-usage contract test passed. The
  focused assertion now checks the delimited `|coverage|` token it names; production
  routing, command order, exit behavior, and every validation stage remain unchanged.
- OBSERVER atomizer predecessor autopsy: the combined meta-plus-ingestion candidate reached
  the base-owned judge before conservative replay and failed SL-016 because base
  `3b93946b856f362f8714803477ac84e2fef4621c` knew only `gict-v1` and `pzg-v1` while the
  candidate ledger already consumed `observer-v1`. Letting candidate code authorize that
  candidate datum would invert the judge boundary. The work therefore split at the
  class-before-instance boundary: this P0 registers the narrow adapter and coarse-replacement
  identity rules with zero OBSERVER ledger consumption; the later theory lane consumes it
  only after this program is a predecessor.
- P0 canonical ingest exited zero with `ledger_changed=false`, `cas_objects_written=0`, and
  the unchanged OBSERVER `gict-v1` coarse fallback. The focused atomizer and alignment suites
  passed 29/29, and the warnings-as-errors solution build completed with zero warnings and
  errors. No BACKFILL, theory source, CAS object, Hearts file, or formalization changed.
- The first P0 ceremony replay reached conservative evaluation but one corpus worker exceeded
  its unchanged 180-second budget while an unrelated `trureturing-fm4` conservative worker
  was simultaneously CPU-active. No timeout or rule changed. After that worker exited, the
  identical clean preimage replay completed: Lean reports 178s, emission 15s, admission 63s,
  and conservative replay 441s; the base-owned actual-tree check contained only the six
  expected SL-022 diagnostics.
- The renewed OBSERVER P0 C0 binds base
  `3b93946b856f362f8714803477ac84e2fef4621c`, clean preimage
  `8f4d98f568182e4747e24c5ad565303f7605784a`, tree
  `f7cec0e9e6b6bee4efa99acb192fc25d60d3f63c`, and certificate SHA-256
  `507a2184a2806bfb8329d7a6b7e7c0009dec54ab30f3e09a0880ef0467d2fe3b`.
  Replay reports 117 golden, 118 total, and six contract cases, preserves 37/37 admits,
  has zero findings, retires no path or rule, and leaves `uncovered_obligations=[]`.

## Residual scan

| Family | Concrete instances | Existing guard | Verdict |
|---|---|---|---|
| Magic numbers and thresholds | `LeanCacheProvisioner.cs:34,47,72` repeats 1800 seconds; `RepositoryRules.Structure.cs:73-94` embeds 600/800/12 policy thresholds; `QuestPdfWriter.cs:31-47` embeds layout values 36/10/19/18/8. | BannedApi checks ambient APIs, not numeric literals. SL-018 covers only the canonical values projection. | `HC-OPEN-001`: no general low-false-positive predicate. The same syntax represents timeout policy, UI design tokens, proof constants, array bounds, and protocol widths. |
| Inline JSON/YAML literals | Synthetic directory-ledger defaults and negative fixtures in `tools/tests/StrataLint.Tests/Rules/RuleFixture.cs`. | Structured canonical writers validate admitted repository artifacts, not arbitrary C# fixture literals. | `HC-OPEN-003`: no machine consumer covers arbitrary C# fixture literals. Malformed-input tests must preserve noncanonical bytes; replacing them with serializers would erase the behavior under test. A global ban would mostly reject valid negative fixtures, so typed fixture builders must be introduced only where they preserve the malformed bytes under test. |
| Environment, path, OS, locale | Fixed tool PATH in `tools/scripts/local-harness-gate.sh`; POSIX `/tmp` in `WorktreeCommandTests.cs:27-82`; `/usr/bin/false` at `FaultInjectionTests.cs:106`. The providerless CLI parse found at `RegistryLoader.cs:137` is now fixed and guarded. | Shell scripts explicitly target Bash; BannedApi now covers culture and ambient time/entropy in all production projects. No declared OS support matrix is machine checked. | `HC-OPEN-004`: without a support contract or a typed temporary-workspace capability, the machine cannot distinguish an intentional POSIX path from an accidental portability bug. |
| Time/tool/version literals | Production harness discovery derives MSBuild `TargetPath`, but workflows, C#, and compatibility fixtures can still copy SDK, central-package, TFM, or Lean version text. Test-only Lean 4.24 fixture strings still differ from the live 4.31 pin. | `tools/StrataLint.Engine/Runtime/SelfTestGovernancePolicy.cs` still compares the BannedApi analyzer package's central version with every lock framework key. The target-framework, SDK-workflow, and general central-package literal scanners do not run; SL-014 remains deferred. | `HC-OPEN-005` expanded: those three copy families have no machine consumer after `46220826c`. That verdict rejected whole-repository text scans because concatenation bypasses them. Future coverage must route SDK, package, and framework identities through typed values that make duplicate authority unrepresentable. `D5-T0010` continues to own broad toolchain compatibility; fixture versions remain open because equality to the live pin would erase compatibility-test intent. |
| Retired canonical literal-duplication families | Ticket/GID pairs, domain/stratum maps, atomizer IDs, specification and Blueprint passages, repository paths, and public-builder defaults can still be copied as bare strings. | None. `AtomizerRegistry.cs`, `RepoPath`, and `RuleId` remain real authorities or types, but no consumer rejects copies elsewhere; `46220826c` deleted the scanners and their red fixtures together. | `HC-OPEN-013`: all listed families currently have no duplication coverage. The deletion verdict found that concatenation trivially bypassed every whole-repository scanner and that TheoryIsolation even hid its own tokens. Correct re-coverage is a typed API that makes each duplicate unrepresentable, following `RepoPath` and `RuleId`, not another after-the-fact text scan. |
| Test snapshots and structural assumptions | Workflow slicing by literal job names at `ReviewRegressionTests.cs:437-439`; CI shell implementation asserted by substrings at `BannedApiCoverageTests.cs:107-119`; duplicated BACKFILL projection snippets at `ReviewRegressionTests.cs:162-167` and `ProductionEnvironmentTests.cs:424-429`. | These tests detect current drift but no guard classifies which assertions are contractual versus brittle implementation snapshots. | `HC-OPEN-006`: snapshot bytes are sometimes the contract. A ban on string assertions or raw fixtures has an unacceptable false-positive rate; typed parsing must be introduced case by case. |
| csproj/props repetition | The same test SDK/xUnit bundle appears in `StrataLint.Tests.csproj:12-17`, `StrataLint.Scribe.Tests.csproj:11-16`, and `StrataLint.ArchitectureTests.csproj:15-21`. | Central package management prevents per-project version copies, but item-group duplication is allowed. | `HC-OPEN-007`: the exact three-project bundle can be centralized in evaluated MSBuild targets, but a generic duplicate-item predicate cannot know project-specific asset metadata. Treat as a scoped build refactor with lock-file verification. |
| Workflow repeated configuration | Five checkout blocks at `.github/workflows/ci.yml:27,131,158,267,275`; job timeouts at lines 24,126,251,264. | The former SDK guard no longer runs; `HC-OPEN-005` owns the missing version-authority coverage. Existing tests check trust topology by substrings. | `HC-OPEN-008`: GitHub Actions repetition can be factored only through composite/reusable workflow boundaries that alter checkout context and the base-controlled trust topology. Textual duplication alone is not a safe predicate. |
| Internal theory references outside managed sources | `docs/develop/theory/` and ingestion/status code intentionally retain the reference inputs and provenance vocabulary; formal/program coupling is a separate semantic question. | SL-016 governs ingestion receipts only. No machine consumer rejects theory references in Lean or non-ingestion C#. | `HC-OPEN-014`: theory-isolation coverage is absent after `46220826c`, whose deletion verdict is recorded under `HC-OPEN-013` -- concatenation trivially bypassed every whole-repository scanner, and this one hid from itself by concatenating its own tokens; `D5-T0036` owns the semantic ruling and whether the obligation remains. If retained, correct coverage must use typed source/provenance boundaries that make reference-source coupling unrepresentable, not another token scan. This ledger does not decide that ticket. |
| Encoded, split, interpolated, or computed duplication | Examples can be manufactured as concatenation, base64, hash lookup, arithmetic, generated code, or runtime I/O. | No general semantic-duplication consumer exists; surviving guards are scoped to their own typed or structured domains. | `HC-OPEN-009`: deciding arbitrary semantic equivalence or whether a computed value has the wrong authority reduces to program/intent equivalence. Every finite text rule has trivial encoding escapes; broadening it produces both bypasses and false positives. |
| Values schema epoch transition | Expand admitted attestation v1 or v2; migrate moved the canonical writer and artifact to v2; contract completed in this PR by removing v1 read support and retaining v1 only as an SL-018 negative fixture (expand-migrate-contract, CLAUDE.md section 6). | The conservative verifier observes a finite base-owned corpus plus the actual trees, not every historically admitted snapshot. | `VALUES-SCHEMA-EPOCH` (open): the active schema epoch/domain is not yet machine-defined, so a later v1 contract can be corpus-conservative without proving the literal universal conservative-extension law. |
| Diagnostic language consistency | English route/parser failures coexist with Chinese SL-021 and bootstrap messages (`Routing.cs:80,85`; `RepositoryRules.Admission.cs:77,82`; `CliApplication.cs:120,124`). Atomizer diagnostics added in this unit are English. | No diagnostic locale/style schema exists; golden cases intentionally bind some current bytes. | `HC-OPEN-011`: terminology and locale are user-interface policy, not a correctness literal. Standardize only with a declared diagnostic style plus an atomic golden-corpus migration; do not mix that migration into registry work. |
| FILEMAP dependency discovery | Machine-readable data can name generated paths through encoding, concatenation, interpolation, aliases, or runtime computation; Lean can express imports outside the current one-module line grammar. | FILEMAP scans decoded TOML/YAML/JSON/Scribe text for concrete generated paths and resolves simple Lean imports. | `HC-OPEN-012`: the active check is an honest low-false-positive subset, not semantic program equivalence. Encoded/computed references and richer Lean import syntax remain detectable only by future structured loaders or compiler-derived dependency edges. |

## MULTI-THEORY-DEBT

Audit scope: every tracked `*.cs` file (including `Blueprint/**/*.scribe.cs`) and every
`.github` workflow/script was scanned on 2026-07-15. No workflow or GitHub script
contains a `D5` literal. The governing basis is specification A1/A2/A7/A10/A11:
`THEORY` is a grammar variable, while M0 admits only D5; SL-021 and `D5-T0009` are the
recorded pressure gate. Per the no-prebuild rule, this section records debt only.

### 1. Already shaped as a current-theory parameter

| Site | Current shape |
|---|---|
| `StrataLint.Engine/Coordinates/Target.cs:35-67` | Every semantic target carries a `Theory` field; printers already project that field rather than a separate lookup. |
| `StrataLint.Engine/Coordinates/Routing.cs:7-15` and `StrataLint.Cli/Commands/ManifestLoader.cs:12-36` | The manifest schema and loader carry `theory` as data. `RouteEngine` then deliberately applies the M0 D5-only SL-021 gate. |
| `StrataLint.Engine/Rules/RepositoryRules.Applicability.cs:75-86` and `StrataLint.Engine/Rules/RepositoryRules.Admission.cs:68-78` | Candidate paths are split to obtain a theory token; non-D5 coordinates are classified as uninstantiated rather than unknown. |

### 2. D5-scoped constants that are legitimate today

| Site | Why it is scoped rather than global debt |
|---|---|
| `StrataLint.Scribe/Values/ValuesKernelDataLoader.cs` and `StrataLint.Scribe/Writers/CanonicalValuesWriter.cs` | These constants bind the D5 values pipeline specifically: D5 Lean truth, D5 kernel data, and the D5 evidence projection. The constant ID set itself lives only in emitter data. A future theory needs its own admitted source before sharing this path. |
| `tools/tests/StrataLint.Tests/Rules/RuleFixture.cs` and `tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml` | The conservative corpus is an explicit synthetic fixture for the sole instantiated M0 theory. Those D5 examples remain valid fixtures after another theory is admitted. |
| `Blueprint/D5/**/*.scribe.cs` and `StrataLint.Scribe.Tests/**/*.cs` | These are typed D5 document data and tests of those documents, not a generic theory registry. |

### 3. Global assumptions that must change when `D5-T0009` opens

Each row is a future migration obligation, not authorization to prebuild the mechanism.

| Site | Assumption to remove at multi-theory admission |
|---|---|
| `StrataLint.Engine/Coordinates/Gid.cs:11,42-47,137-304` | Parsing and physical-path construction force a single `Theory = "D5"`, even though `Target` already stores theory. Parse `THEORY` from the surface and preserve it through every plane inverse. |
| `StrataLint.Engine/Coordinates/Routing.cs:62-80,145-249,282` | Paper/experiment IDs, every routed GID prefix, and the formal mirror skeleton are emitted with D5 literals instead of `ManifestSyntax.Theory`. |
| `StrataLint.Engine/Coordinates/RepositoryPathPolicy.Paths.cs:19-180` and `StrataLint.Engine/Coordinates/RepositoryPathPolicy.cs:221` | F/B/E/C/L/P physical-path inverses and controlled-domain recognition assume the theory directory is D5. |
| `StrataLint.Engine/Coordinates/RepositoryPathPolicy.cs:9` and `StrataLint.Engine/Rules/RepositoryRules.Admission.cs:13` | The assumption registry and axiom-debt paths are single global D5 paths rather than theory-scoped addresses. |
| `StrataLint.Scribe/Ast/GidRef.cs:40-49`, `Ast/DocumentHeader.cs:99`, `Ast/DefinitionDsl.cs:11`, and `Emission/DocumentDefinitions.cs:83` | Plane classification, mirror derivation, and source-path bijection slice or prepend the literal `D5` instead of using the parsed target theory. |
| `StrataLint.Engine/Rules/RepositoryRules.Applicability.cs:14,36-40`, `Rules/RepositoryRules.Helpers.cs:15,50-57`, and `Admission/LeanModels.cs:113-115` | Managed formal files and domain-scoped artifacts are recognized only under the D5 root. |
| `StrataLint.Engine/Rules/RepositoryRules.Structure.cs:11,18,108-109,181,216-223` | Hearts, managed imports, mirror prefixes, and domain validation are fixed to D5 rather than the artifact's theory. |
| `StrataLint.Engine/Rules/RepositoryRules.Content.cs:154` | Generic evidence-GID diagnostics identify the E plane with a `D5/E/` prefix. The D5 values checks at lines 230-238 remain category 2. |
| `StrataLint.Engine/Rules/RepositoryRules.cs:30,39,43`, `Coordinates/DomainTypes.cs:128`, and `Rules/Backfill/BackfillInventoryRule.cs:11,15,283` | Task, query, case, and frontier discovery implement D5-shaped identifiers instead of the `THEORY-T/Q` grammar. |
| `StrataLint.Engine/Coverage/CoverageAnalyzer.cs:83`, `Dag/TruthDagConstruction.cs:177-178`, and `Snapshot/CanonicalSnapshot.cs:96` | Artifact classification, managed-module recognition, and structured evidence canonicalization enumerate D5 as the only admitted theory. |
| `StrataLint.Engine/Ledger/FrozenContentAddress.cs:12,16,175,182` | Frozen task/assumption references and Lean import discovery recognize only D5 case and assumption namespaces. |
| `StrataLint.Cli/Admission/ProductionCliEnvironment.cs:247-251` | The production self-test proves only a D5 route. It must probe the admitted theory set once that set has more than one member. |

## Standard action for a new family

1. Name the authority that should own the value and the exact consumer scope.
2. Preserve one real stock instance and add the smallest synthetic rejecting fixture.
3. Run the targeted fixture and observe the expected red state.
4. Implement the narrowest structural/semantic predicate that rejects the stock and
   fixture while retaining explicit green counterfixtures.
5. Repair stock to consume the authority; do not add a second allowlist as a shortcut.
6. Re-run targeted red/green evidence, the full .NET build/tests, and the baseline gate.
7. Update this matrix and either close the `HC-OPEN-*` item or record the remaining
   escape, false-positive boundary, or cost. Failures and abandoned approaches stay in
   the audit log or task autopsy.

The stopping rule is not "search returned zero." It is: every observed instance is
guarded, repaired, or present in this open ledger with an explicit reason.

## DIGESTION-LEDGER-EPOCH (active, 2026-07-15)

This epoch moves digestion preimages from mutable theory volumes into a replayable
content-addressed ledger without weakening an already admitted path. Its stages are
deliberately split so the expand judge remains conservative and the later contract pays
for its protection-surface change explicitly.

| Segment | Status | Machine boundary and close condition |
|---|---|---|
| E1 expand | **complete** | Schema 3 accepts optional `cas_ref`; canonical raw bytes live at `Meta/Digestion/atoms/sha256/<64-lower-hex>`. The judge verifies ref/path/blob/raw-fingerprint equality plus missing, corrupt, and orphan blobs. A CAS-backed receipt no longer needs volume reconciliation; a receipt without `cas_ref` follows the unchanged #109 path. Theory and CAS bytes may be opaque, ingest writes CAS refs, and source-format failure produces one reported whole-source coarse atom once that source's existing receipts are CAS-backed. I/O, schema, CAS, hash, and atomizer-integrity failures still block. The CAS object directory is outside SL-003 code-bucket capacity but only for canonical addresses. |
| E2 migrate | **complete** | All 789 current GICT/PZG receipts (81 GICT, 708 PZG, including 769 residual-open) and all 12 `atomizer: none` specification receipts now bind exact raw CAS bytes through `cas_ref`. The specification receipts retain their 12 byte boundaries and source reconciliation for `SPEC-ZERO-ANCHOR`; no reader is contracted here. The canonical stock test requires every current receipt preimage and the CAS judge proves zero orphan, dangling, or hash-mismatched objects. A repeated `make ingest BASE=origin/dev` wrote zero objects, reported `ledger_changed=false`, and preserved the ledger SHA-256 byte-for-byte. |
| E3 contract | **pending** | Only after E2, the E3-specific P1 plan, and the separate specification-receipt case close, consume that plan once to remove the boundary/stale/source-content/atomizer admission readers, make theory a non-bearing reference class, and remove transitional schema fields in one certificate-bearing contract change. |

E1 changes no canonical digestion-ledger entry and no golden corpus case, so it needs
no C0 renewal. `SPEC-ZERO-ANCHOR` remains a separate 12-receipt obligation: move those
normative specification spans to typed conformance cases or another independently
admitted receipt form before E3; this epoch does not silently recategorize the spec as a
free-form theory volume.

### E1 implementation autopsies

- The first flat CAS shape inherited SL-003's 12-file code-bucket ceiling and would have
  blocked E2 at object 13. Canonical CAS paths are now excluded from module line/directory
  capacity; malformed neighbors retain the old closed-world rejection.
- One digest-status fixture consumed `DigestionIngestPlan.Document` but discarded the
  plan's `CasObjects`, creating a ledger that correctly failed as dangling. The fixture
  now mirrors production's paired document+object snapshot, and the missing-blob guard
  remains unchanged.
- The initial writer created CAS files before the final BACKFILL write but did not undo
  them when that write failed. Because current snapshots include untracked files, the
  leftovers became unrecoverable orphans on retry. The writer now rolls back only paths
  newly created by that invocation; existing append-only blobs are never deleted. The
  final ledger is flushed to a same-directory temporary file and atomically replaced, so
  an I/O failure before commit cannot expose partial `cas_ref`s.

### E2 migration close (2026-07-16)

`make ingest BASE=origin/dev` captured 782 source-reproducible theory atoms plus all 12
manual specification spans. Seven acknowledged-stale theory receipts no longer had a
preimage in the current volumes; their exact raw bytes were replayed through the current
atomizers from the git audit chain (six from `76cae68`, one from `80a9836`) and accepted
only after each computed SHA-256 equalled the frozen ledger fingerprint. A canonical
ingest then removed the seven obsolete stale acknowledgements. The final inventory is:

- GICT: 81/81 CAS-backed, comprising 16 partial-open and 65 residual-open receipts.
- PZG: 708/708 CAS-backed, comprising 4 partial-open and 704 residual-open receipts.
- Specification: 12/12 CAS-backed, with all 12 legacy boundaries retained; two remain
  partial-closed and ten partial-open under the unchanged specification reconciliation.
- CAS: 801 referenced objects for 801 receipts; `digest-status` reports 801 entries,
  zero deletable now, and no findings.

The first complete pass reported `cas_objects_written=794 ledger_changed=true`. After
the seven historical preimages were restored, the canonicalizing pass reported zero new
objects and removed the stale acknowledgements. The next full pass reported
`cas_objects_written=0 ledger_changed=false`; `Meta/BACKFILL.yaml` remained byte-identical
at SHA-256 `ebc129e37e895b934e0f87ab0419cd13d45614674dd9e1958653b842e7ca5483`.
After integrating the legitimate Scribe receipt updates from dev merge `94fcbc4`, another
full ingest again reported zero objects and `ledger_changed=false`; the merged ledger is
byte-stable at SHA-256 `5504d4bf780086ec092c85ef4efdff556461b08cc3035e6c466d7e3da307e672`.

E2 also closes the specification-CAS ambiguity exposed by E1: CAS-backed receipts from a
registered theory atomizer may remain independent of a mutable theory volume, while an
`atomizer: none` receipt continues to require and verify its source byte boundary. Paired
fixtures preserve both sides of that distinction.

One auxiliary `shasum` replay initially failed before reading data because the inherited
`C.UTF-8` locale is unavailable on this Darwin host. Re-running the same seven-object
check under `LC_ALL=C LANG=C` succeeded with every filename equal to its content hash;
the canonical CAS judge remains the platform-independent admission authority.

The first full `make test` stopped at TheoryIsolation because an admission fixture named
the registered adapter through its theory-specific `GictId` symbol outside the Digestion
test boundary. The fixture now selects `AtomizerRegistry.RegisteredIds[0]`, which tests
the same registered-versus-none contract without leaking an internal theory token; the
original architecture red test and both paired SL-016 fixtures pass together.

The first full `make gate BASE=origin/dev` passed its candidate build, 784 tests,
selftest, both Lean inspections, and emission check, then stopped before admission with
an ancestry infrastructure failure: its mandatory fetch advanced `origin/dev` from the
E1 merge `806494e` to the newly landed describe-node merge `94fcbc4`. E2 integrates that
new baseline and reruns the same gate; pinning the stale base would have hidden a real
concurrent predecessor instead of proving a conservative extension over current dev.

The next gate reached admission and exposed one content violation before SL-022:
the new no-atomizer ingest fixture had pushed `DigestionAlignmentTests.cs` from below
the SL-003 ceiling to 821 lines. The fixture moved intact to the focused ledger suite;
the alignment suite is now 783 lines, the ledger suite remains below capacity, and the
direct admission probe returns only the expected protected-surface exit 3. No test or
capacity rule was weakened to obtain that routing.

### OBSERVER-QUANTUM split close (2026-07-17)

Reconnaissance chose the explicit-adapter branch, not a GICT dialect extension. The source
has one title, a subtitle, an abstract, ten numbered sections, and an appendix. Its semantic
locators are 24 exact bold leads plus seven prose paragraph leads; it has no GICT-style
numbered Definition/Theorem/Comment claim grammar. Reinterpreting those labels as new GICT
claim kinds would couple unrelated dialects. `observer-v1` is therefore a narrow adapter for
this production volume only; `gict-v1` and `pzg-v1` retain byte-identical semantics, and no
generic atomizer platform was introduced.

The 31 claim locators are complete and ordered by source bytes. Their families are:

- scope 2, premise 3, theorem 4, measurement 3, classical 4;
- probability 4, freedom 4, observer 2, physics 2, verdict 3.

The first canonical ingest reported
`stale_acknowledged=1 residual_open_added=31 coarse_fallbacks=0`,
`cas_objects_written=31`, and `ledger_changed=true`. It retained the original whole-source
receipt as stale with `cas_ref`
`sha256:c74925a3c3098b691503837f567abdaf6ff527a9a36934061c90a00fa7732a91`;
that CAS object's SHA-256 still equals the untouched source's SHA-256. The 31 fine claims
each have a new content-addressed CAS object. No theory source, Hearts file, or formal Lean
artifact changed.

The final `digest-status --json --base origin/dev` reports 869 entries repository-wide and
zero deletable now. The OBSERVER source contributes 32 entries: 31 are
`seen/residual/open/deletable=false`; the retained coarse receipt is
`stale/residual/open/deletable=false`. A repeated full ingest after predecessor integration
reported `stale_acknowledged=0 residual_open_added=0 coarse_fallbacks=0`,
`cas_objects_written=0`, and `ledger_changed=false`; the stable BACKFILL SHA-256 is
`1ef44db94ad4122f96c4ee617e0ff844edfb983e1d09c69294b3842c5be440da`.

Fail-closed review hardened both dialect recognition and stale history. Unknown or indented
bold leads, malformed Q1-Q4/settled/open labels, and duplicate locators are rejected. The
coarse replacement obligation is owned by the baseline source identity: source rename or
relocation, `observer-v1` to `none`, stale-acknowledgement removal, atom/path/fingerprint/CAS
identity mutation, and a coarse CAS clone under any source are rejected. The
last independent review found the pre-settlement source-id escape; binding obligations from
the complete baseline source set closed it. The current focused atomizer/alignment suites
pass 29/29.

The first combined meta-plus-data gate failed before conservative replay because base
`3b93946b` did not know candidate-only `observer-v1`. This was not bypassed. PR #150 installed
`OBSERVER-ATOMIZER-P0` with zero OBSERVER ledger consumption, renewed C0, passed all three
required checks, and auto-merged as predecessor `198d3140`. The first content C0 bound base
`198d314016495bc41d68323f495c1cfee0ed1e98`, clean preimage
`721eef3a7055e18f4726bd93f7275c6aa970e460`, tree
`db77899485138ece2d546b058e1dd22ddb078183`, and certificate SHA-256
`22f15c36c091bcd8b83ecfe32ced23a60881d485685b9e8e8a8c74f7ad55f3cf`.
Replay reports 117 golden, 118 total, and six contract cases, preserves 37/37 admits, has
zero findings, retires no path or rule, and leaves `uncovered_obligations=[]`. Its measured
stages were 193s Lean reports, 17s emission, 85s admission, and 405s conservative replay.

The first post-ceremony preflight's mandatory fetch advanced `origin/dev` through PR #149
from `198d3140` to `f231f7f4`; that new base was not an ancestor of the candidate, so the
already-doomed Lean pair was stopped rather than misreported as an acceptance run. The
branch merged that exact predecessor without rebase. Its O-6 source receipts occupied a
different BACKFILL region: the next full ingest again wrote zero CAS objects, reported
`ledger_changed=false`, and preserved the 31 seen plus one stale OBSERVER alignments.

The final renewed C0 binds base `f231f7f40497cee3e06b0f7db95355fbeae52e2a`,
clean preimage `f495bee4ee6937fe6bd552f966d92621d84493f0`, tree
`5efd4743a113b7bfc99faaee0050e52bbc1ceb20`, and certificate SHA-256
`777b3f3e18c98c641315acaa9e3330be5087fd40879e27e06a00791985dab3e7`.
Replay again reports 117 golden, 118 total, and six contract cases, preserves 37/37 admits,
has zero findings, retires no path or rule, and leaves `uncovered_obligations=[]`. The
renewal measured 190s Lean reports, 18s emission, 84s admission, and 395s conservative
replay.

The first full preflight after that renewal passed all three .NET test assemblies (706/706,
135/135, and 125/125), the warnings-as-errors build, selftest, compile-fail proofs, paired
Lean reports, emission checks, base admission, and candidate build. It then failed only at
`verify-conservative`: one corpus worker exceeded the unchanged 180-second process budget;
the conservative stage took 263s and the full preflight 548s. Contemporaneous process
evidence showed macOS `mds_stores` using about 97-147% CPU and an unrelated competing `dotnet`
testhost using about 92-94% CPU, with no second conservative worker. No rule or timeout
changed; the identical canonical preflight must be retried after the competing testhost exits.

A later no-contention replay reproduced the same 180-second worker failure and falsified
contention as the complete explanation. Darwin's bare `mktemp -d` ignored an exported
`TMPDIR=/private/tmp` and still placed the outer judge and baseline harness under the indexed
`/var/folders` tree; an explicit template placed it under `/private/tmp`, where the identical
pinned-base verifier emitted `CORPUS_CONSERVATIVE`, preserved 37/37 baseline admits, and
reported `findings=[]`. The local gate now passes `${TMPDIR:-/tmp}` to an explicit mktemp
template, preserving its default while making the documented non-indexed replay selectable;
the conservative worker budget and every admission rule remain unchanged.

Two auxiliary-probe failures changed no canonical bytes. Darwin rejected inherited
`C.UTF-8` before a hash probe read its input; the replay used `LC_ALL=C LANG=C`. A manual
CAS-payload concatenation probe also exposed blank-line gaps because non-claim headings and
inter-claim whitespace belong to the atomizer's ordered scaffold slices, not claim CAS
payloads. The production `Reassemble()` path joins all slices and passes byte-exact source
reconstruction; no blank line was added to or removed from the source or CAS.

Literature leads are candidate-only, unattested, and metadata-unverified. They create no
coverage or literature receipt, and no DOI is asserted in this batch:

- `gleason1957-measures`, `born1926-quantenmechanik`, `bell1964-epr`;
- `clauser-horne-shimony-holt1969`, `kochen-specker1967`,
  `zurek1981-pointer-basis`, `zurek2003-decoherence-einselection`;
- `ollivier-poulin-zurek2004-quantum-darwinism`,
  `connes-rovelli1994-thermal-time`, `pusey-barrett-rudolph2012`;
- `frauchiger-renner2018`, `bong-et-al2020-local-friendliness`,
  `conway-kochen2006-free-will`, `bost-connes1995-hecke`.

## DIGESTION-PHASE2-INGEST (complete, 2026-07-15)

After PR #109 supplied cross-syntax receipt identity and one-step legacy conversion,
`make ingest` completed the Phase 2 extract→identify→subtract→residual pass for the
PR #106 theory volumes. It migrated all 20 atomized legacy receipts to the then-current
structured identity (GICT 16, PZG 4), while leaving the 12 `atomizer: none`
specification receipts unchanged. The resulting alignment and ledger write recorded:

- seen: 15
- stale acknowledged: 5 (`gict-hearts-o5-o6`, `gict-constant-Cphi`,
  `gict-constant-T0`, `gict-constant-delta-mean`, `gict-constant-c1`)
- residual-open added: 737 (GICT 55, PZG 682)
- ledger changed: true

### First-voyage autopsy (REFERENCE-ZERO-ANCHOR migrate, 2026-07-15)

`make ingest` did not reach a ledger write. With the production ledger unchanged, its
legacy byte spans point into the new theory bytes; the first truncated UTF-8 span
fails during digest-status evaluation. A minimal data-only trial converted only the 20
GICT/PZG receipts to the then-current structured identity and left all 12 `atomizer: none`
spec receipts untouched. That exposed the alignment counts but was also rejected by the
base-owned judge:

- seen: 15
- intended stale: 5 (`gict-hearts-o5-o6`, `gict-constant-Cphi`,
  `gict-constant-T0`, `gict-constant-delta-mean`, `gict-constant-c1`)
- reported residual-open frontier: 737

The count is 737 rather than the expected version delta of about 165 because the
aligner subtracts only registered receipt paths, not the 587 claims atomized from the
baseline theory volumes. More importantly, stale admission requires the candidate
receipt preimage to be byte-equal to `origin/dev`; the structured replacement receipt
cannot be byte-equal to its legacy preimage. The second `make ingest`
therefore failed on exactly the five receipts above with `INGEST_INVALID`, and wrote
nothing. No data-only state can both retain those five as actual acknowledged stale
receipts and pass the `origin/dev` baseline comparison. The trial ledger edit was
removed; this item remains open for an expand-side cross-syntax identity/conversion fix.

### Gate-close autopsy (attempt 3, 2026-07-15)

The first successful ledger write exposed a cross-rule false positive at the full gate.
SL-019 scanned every governed structured scalar for the bare substring `tension`, while
the atomizer's canonical `extension-table/6.38′` locator contains that substring.
`make ingest` validates its final ledger through SL-016, so this conflict appeared only
when the complete rule set ran. The narrow repair excludes only `tension` immediately
preceded by `ex`; a paired regression proves that the extension locator is accepted
while an explicit `unresolved tension` signal remains rejected. No receipt identity or
theory locator was renamed to evade the judge.

Because admission executes the judge from the dev baseline, a candidate-only repair
could not validate this migrated ledger: the unchanged base judge rejected BACKFILL
before conservative replay could certify the candidate judge. The two-file repair
therefore landed independently through PR #110 and its protected-surface gate, after
which this branch merged the repaired dev judge and reran the complete acceptance chain.

### DESCRIBE-NODES gate autopsy (2026-07-15)

The first full gate found two integration debts that the compile and test targets do not
exercise. Five new Describe and L-plane test files raised the
`StrataLint.Scribe.Tests` root from 12 to 17 files, so SL-003 rejected the directory.
They were moved without content changes into the pressure-created `Describe/` bucket,
leaving both directories within the 12-file bound.

The same gate found all 12 `atomizer: none` specification receipts displaced after the
A12/A17 additions. `make ingest` failed before a ledger write because that command
requires these manually delimited receipts to resolve before it plans atomized-source
updates. Following the established `3faf952` rebind precedent, every unchanged sample
span was shifted by the measured 1,882-byte offset while its two fingerprints remained
unchanged. A targeted base-harness admission then returned protected-surface exit 3
with only SL-022 diagnostics and no blocking content diagnostic.

## HEARTS-AUTH-P0 (complete, 2026-07-17)

- The superseded cryptographic review returned `CRITICAL`: without a signature or authenticated issuer, a committer can append a false authorization row; that finding is technically correct.
- The 2026-07-17 user ruling overturned it under CLAUDE.md rule 20 and public-Git-history economics: prevention cost exceeds the value of preventing a visible forgery.
- Distributed clones make history tampering observable, so false judgments go through detection, appeal, correction, and accountability rather than prior cryptographic gilding.
- The admitted table records only date, quoted authorization, fully qualified declaration name, and canonical statement SHA-256; SL-008 requires every baseline declaration unchanged and exactly one matching addition.
- Missing authorization, hash drift, piggybacking, malformed rows, and historical deletion/rewrite remain hard failures; signature, issuer attestation, identity check, nonce, replay state, and authorization consumption do not exist.

## UNCONSUMED-ARTIFACT-AUDIT round 1 (2026-08-17)

Recorded so that round 2 has something to diff against. Spec 11.24 makes the stop
criterion `two consecutive full audits with zero new gaps`, and requires the round
count and new-gap curve to be kept; without a round-1 record the criterion cannot
be evaluated at all.

Input version: `bf0d97896` for the round as a whole. **The C# member reachability row is
the exception: it was measured at `28c0ecf77`**, which is where PR #2114 records the census
baseline. `bf0d97896` already contains the merges that acted on those findings (`cd617baf1`
for the seventeen zero-reference deletions, `be999cc93` for the twenty-four test-only
dispositions), so it cannot reproduce that row and must not be used to calibrate a rebuild.
Method: per-surface enumeration, each surface reduced to a machine reading before any
deletion. Confirmed gaps are candidates that survived
independent verification and were merged as deletions or registered as named opens.

| Surface | Reading | Confirmed gaps |
|---|---|---|
| Shell functions and scripts | 115 functions, 15 scripts, zero-call 0 | 0 |
| NuGet packages | 11 central versions, every one referenced by a csproj | 0 |
| C# member reachability | raw 7713, mechanical false positives 99.46%, true candidates 42 | 42 |
| Prose path references | 162 raw, minus reserved coordinates, mathlib paths, globs and dated reports | 1 |
| CLI verbs | 24 registered, only `validate-blueprint-pins` had no data, doc or caller | 1 |
| Test-tree support types | 77 non-test types, zero-reference 5, false positives 4 | 1 |
| `.github/` | every referenced script exists; `STRATALINT_TIMING` is consumed by `harness-gate.sh` | 0 |
| `Library/` | 34 anchors, 33 cited; `bell1964epr` is an under-citation in a live Bell module, not an orphan | 0 |
| `skills/` | install contract in each `SKILL.md` plus use receipts in three reports | 0 |
| `docs/reports/**` | 25 named diagnoses, sole copy of their conclusions; dossier, not projection | 0 |

Merged this round: 13 pull requests, net 1474 lines removed. The two largest were
whole machines guarding something that was not there: `BlueprintPins` validated a
manifest format with no instance in the repository, and the ticket index mirror
carried 78 lines of validation whose three checks only guarded the mirror itself.

Six named opens were registered rather than deleted, each with a closing condition:
`D5-T0035` through `D5-T0040`.

**Round 2 must repeat every surface above on a later input version and report the same
table.** Two consecutive rounds of all-zero confirmed gaps reach the fixed point; any
non-zero row restarts the count. A surface whose classification is inherited from this
round does not count as an independent challenge.

Eleven further surfaces were measured after the table above was recorded. They belong to
the same round and carry the same round-2 obligation.

| Surface | Reading | Confirmed gaps |
|---|---|---|
| Makefile targets | every target reachable; dependency graph changed so `test`/`lean`/`lean-report`/`build` no longer depend on `lean-cache-ensure`: the canonical `lean-cache-run.sh` wrapper owns the ensure for each Lean process, while `lean-cache-ensure` remains an optional explicit prewarm | 0 |
| `Meta/domains.yaml` | 50 domains, every one has objects under `D5/` or `Blueprint/` | 0 |
| `Golden/Projection` | 2 files, 3 consumers each | 0 |
| `Evidence/D5` | 1 file, 11 consumers | 0 |
| `Meta/Digestion/atomizers.toml` | every entry has an implementation | 0 |
| CAS atom store | orphans are already fail-closed at `DigestionCasStore.cs:127` with a red fixture | 0 |
| `registry.yaml` `artifact_kinds` | `csv` has no object but is a reserved member of the Evidence GID `--tag` alphabet | 0 |
| spec code symbols | `FrozenLedgerBaseWriter` is a component Part 12 plans but has not built; `LatexStatement` appears only inside a correct negative claim | 0 |
| spec Part 12 roadmap | P0-F1 and PR-A have landed, PR-C has not; unbuilt stages are the normal content of a labelled implementation contract | 0 |
| `agents/` charters | 11 files, each externally referenced and registered in `registry.yaml` | 0 |
| **spec glossary claim** | `Meta/glossary.csv`, its papergen consumer and its drift lint all absent | **1** |
| Duplicate-implementation lens | 2792 method bodies, 8 cross-file exact duplicates; duplication is a second-source defect, not an unconsumed artifact | 0 |

The last row is the independent challenge required before the fixed point: a lens that does
not inherit this round's classification, returning zero for this front's own definition.

Three of those zeros come from a criterion rather than from finding nothing. Between a
zero-reference reading and a deletion sit three questions: is it a reserved coordinate, is it
a planned component, is it a correct negative claim. Each of the three saved something here.
