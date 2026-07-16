# Hard-code guard and residual ledger

> **Maintenance contract:** every newly discovered hard-code family must update this
> ledger in the same change. If a low-false-positive predicate exists, fix the stock,
> add the guard, add an executable rejecting fixture, and update the matrix. Otherwise
> add or refine an `HC-OPEN-*` entry with concrete examples and the reason it cannot be
> judged honestly. A green repository is never, by itself, a proof of "no hard-coding."

Audit baseline: `origin/dev` at `4f2d166` (PR #95, theory-zero), audited on
2026-07-14 from `harness/hardcode-audit`.

## Answer

No. PR #95 removed internal theory families from the formal/program layer and added a
machine tripwire against their return. The repository now has several strong, narrow
hard-code guards; it does not have, and cannot honestly claim, a general proof that no
hard-coded value remains. Literal intent, semantic duplication, encoded values, and
test-fixture structure remain partly or wholly outside those predicates.

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
| BACKFILL pair duplication policy | All tracked C# is scanned for an exact registered `case_id` and GID pair in six dictionary/tuple shapes (`CanonicalSourceDuplicationPolicy.cs:33`). | Yes: `CanonicalTicketDictionaryEntryIsRejectedByTheRedFixture`; three shapes passed in the 31-case CanonicalSources run. | Copied `Meta/BACKFILL.yaml` ticket maps in the recognized syntax shapes. |
| Domain/stratum duplication policy | All tracked C# is parsed with Roslyn; a dictionary indexer mapping a registered domain literal to `S0` through `S4` is rejected (`CanonicalSourceDuplicationPolicy.cs:69`). | Yes: `RegisteredDomainDictionaryEntryIsRejectedByTheRedFixture`; `S0` and `S4` passed. | Copied `Meta/domains.yaml` mappings in one syntax shape. |
| Atomizer identifier duplication policy | Atomizer identifiers loaded from `Meta/BACKFILL.yaml` are rejected in tracked C# string literals outside `AtomizerRegistry.cs`; the registry is the sole dispatch authority. | Yes: `LedgerAtomizerIdLiteralIsRejectedByTheRedFixture`; the registry-owner counterfixture also passed. | Ledger atomizer IDs copied into C# dispatch or fixture text instead of using `AtomizerRegistry`. |
| Specification passage duplication policy | Tracked C# and repository TOML reject exact copied specification passages of at least 64 characters and 24 CJK characters (`CanonicalSourceDuplicationPolicy.cs`). | Yes: `LongExactSpecificationPassageIsRejectedByTheRedFixture` covers C# and TOML; short and rewritten text is the green counterfixture. | Long Chinese passages copied byte-for-byte from the mutable canonical specification into code or corpus fixtures. Reworded text, non-CJK passages, encodings, and other file formats remain outside this narrow predicate. |
| Golden corpus storage policy | All tracked C# is parsed with Roslyn; a literal-name `new GoldenCase(...)` or legacy literal-name `C(...)` inside `GoldenCorpus` is rejected (`GoldenCorpusStoragePolicy.cs`). Canonical case bytes are loaded only from `Meta/StrataLint/Golden/cases/*.toml`. | Yes: `CSharpGoldenCaseDeclarationIsRejectedByTheRedFixture` covers both old construction shapes; `SchemaDeclarationIsNotMistakenForCaseData` is the green counterfixture; the repository/TOML authority tests passed. | Golden case names, mutations, changes, and expected diagnostics embedded in C# instead of the TOML authority. The predicate deliberately permits schema construction from parsed variables. |
| FILEMAP custody and producer policy | `Meta/FILEMAP.toml` is parsed fail-closed; every tracked/unignored path matches exactly one pattern, registry root files equal tracked root files, generated files match the producer inventory plus `emit-check`, data names an existing program verifier, and class directories remain pure. Residence policy states the no-data-under-`Meta/StrataLint/` ideal while marking and counting the current epoch violations. | Yes: unclassified, ambiguous, registry drift, missing loader, missing/mismatched producer, missing generated `produced_by`, directory mixing, unmarked protected-surface data, exact residence inventory drift, data-to-generated reference, and Lean-to-generated import red fixtures. | Hand-maintained or implicit file ownership, generated outputs without an executable producer/check, and unmarked or newly added protected-surface data. The bounded dependency predicate remains recorded under `HC-OPEN-012`; the frozen current violations remain open under `RESIDENCE-EPOCH`. |
| Repository path literal policy | All tracked C# string literals are checked. A value with at least two `/` characters that exactly names an existing file is rejected unless it directly defines a `const string` (`RepositoryPathLiteralPolicy.cs:22`). | Yes: `ExistingMultisegmentPathLiteralIsRejectedByTheRedFixture`; green const and nonexistent-path counterfixtures also passed. | Consumers copying existing repository file paths. |
| Default injection policy | Effectively public members on effectively public `*Dsl` or `*Builder` types may not use a literal GID, case ID, or canonical anchor as a parameter default (`DefaultInjectionPolicy.cs:20`). | Yes: `CanonicalLiteralDefaultIsRejectedByTheRedFixture`; GID and case variants passed. | Hidden canonical policy injected through public defaults. |
| Theory isolation, sources | All Lean and all non-ingestion C# reject internal theory paths and the retired theory-family tokens; Lean task autopsy text and the ingestion whitelist are explicit exceptions (`TheoryIsolationPolicy.cs:46,76`). | Yes: Lean header, non-autopsy task, and C# citation negative fixtures passed. | Formal/program code coupled to internal theory reference sources or numbering families. |
| Theory isolation, generated catalog | Parsed generated anchor definitions reject retired internal theory schemes (`TheoryIsolationPolicy.cs:104`). | Yes: `CatalogTheorySchemeIsRejectedByTheRedFixture` passed. | Generated catalog reintroducing internal theory schemes. |
| External anchor catalog consistency | Typed catalog entries must be external literature/mathlib anchors, exactly equal the external manifest, with property names derived from the anchor (`AnchorCatalogConsistencyTests.cs:8`). | Yes for name transform: `MismatchedExternalAnchorPropertyNameIsRejectedByTheRedFixture`; repository equality checks are live tripwires. | Hand-copied anchor identity and drift between manifest and typed catalog. |
| C0 ceremony trust root | Recursive controller/corpus/gate source sets, Git blob OIDs, certificate SHA-256, preimage commit/tree, and implication counts must match live bytes (`C0CeremonyTrustRootTests.cs:68`). | Partial: recursive-discovery synthetic fixtures exist; byte/address mismatch has no isolated synthetic fixture. The repository-bound tripwire passed. | Unattested changes to the conservative-extension controller, corpus, gate wiring, or inaugural certificate. |
| Contract-epoch obligation accounting | Bootstrap protection matchers and active-rule descriptors emit one canonical policy root; the base-owned comparator reads exact-commit append-only events and content-addressed receipts, computes the complete retirement delta, and rejects nonempty `uncovered_obligations`. Candidate registrations have no same-comparison authority; base plans are one-shot and cannot target the authority ceiling. | Yes: exact-path/schema, store closed-world/hash/C0, base-versus-candidate evidence, same-PR declaration, candidate-plan consumption, glob, out-of-delta, missing coverage, double-consumption, opaque shrink, and unshrinkable-root tests plus six canonical corpus cases. | Implicit or changed-path-only protection policy, reusable exception lists, candidate-authored subtraction authority, and retirement of verifier/gate/frozen trust roots. P0 carries zero registered declarations. |
| Central package version literal policy | Every tracked C# string literal exactly equal to a `Directory.Packages.props` version is rejected; an empty/malformed central version set fails closed (`CentralPackageVersionLiteralPolicy.cs:15,28,43`). | Yes: copied-version and empty-catalog red fixtures; the real `5.6.0` copy failed before stock repair. | Exact C# copies of central NuGet versions. |
| .NET SDK single-source policy | Every parsed `.github/workflows/*.{yml,yaml}` `actions/setup-dotnet@*` step (case-insensitive action identity) must use `global-json-file` and must not contain `dotnet-version`; the canonical CI workflow must contain both candidate/baseline global-json references (`DotnetSdkSingleSourcePolicy.cs:9`). | Yes: mixed-case copied-version, additional-workflow copied-version, and missing-baseline red fixtures; both real workflow copies failed before repair. | Workflow copies or ambient omission of the SDK version pinned by `global.json`. |
| .NET target-framework single-source policy | C#, project/build files, scripts, workflows, and structured config reject any `netN.N` literal outside `Directory.Build.props`, generated lock files, and the dedicated synthetic lock-key fixture (`TargetFrameworkSingleSourcePolicy.cs`). The base-owned gate resolves each CLI `TargetPath` through MSBuild and passes both absolute harness paths to the verifier. | Yes: `CopiedTargetFrameworkIsRejectedByTheRedFixture`; the owner/generated/synthetic whitelist counterfixtures and repository scan passed. | TFM copies in runtime path discovery. It does not prohibit prose or generated lock projections and does not replace the broader deferred SL-014 toolchain policy. |
| Values constant-set ownership | Engine validates canonical v2 projection schema, status/receipt shape, input attestation, unique sorted IDs, and complete Lean provenance without owning the ID set or kernel names. Scribe loads a non-empty, unique, sorted catalog of any size from `values-kernels.toml`; canonical re-emission is byte-exact. | Yes: the two-item projection, synthetic future-kernel, and one-row TOML fixtures each failed against the former C# copies before repair. Production writer byte-stability and current catalog-content tests remain authoritative for today's 14 rows. | Constant identity/cardinality and computation selection copied from the emitter data into the Engine or loader. It does not make arbitrary projections canonical: input hashes and `emit-check` still bind output to TOML/Lean. |
| BannedApi culture matrix | The official semantic analyzer consumes an exact, duplicate-free 143-member culture-sensitive denylist in Engine, Scribe, and CLI; project, central version, actual lock framework keys, and lock attachment are checked (`BannedApiConfigurationTests.cs:9`, `BannedApiCoverageTests.cs:35`). | Yes: missing-analyzer, duplicate-central-version, and synthetic `net99.0` lock fixtures plus compile-fail proof. Attaching it to CLI made providerless `int.TryParse` fail with the sole RS0030 before repair. | Providerless numeric/temporal parse, try-parse, and formatting overloads in production projects. |
| BannedApi nondeterminism matrix | Engine, Scribe, and CLI consume the exact 7-member ambient clock/entropy/tick denylist. Engine and Scribe also consume the one-member GUID denylist; CLI is outside that GUID predicate because it allocates ephemeral workspaces (`BannedApiCoverageTests.cs:56`). | Yes: compile-fail proof lines 9-16; the complete proof produced exactly 18/18 RS0030 diagnostics. | Ambient runtime nondeterminism in all production projects; GUID creation in deterministic Engine/Scribe code. It does not prove every future CLI GUID use is ephemeral. |
| SL-004 Mirror completeness | `mirror-B` and `mirror-E` header fields, when not `none`, must have the matching `D5/B/` or `D5/E/` address family and resolve to an existing projection (`RepositoryRules.Structure.cs:98`). | Yes: active-rule `mirror` mutation passed by deleting the referenced Blueprint. | Hand-copied formal-to-projection addresses; it checks existence and address family, not content equality. |
| SL-006 Generated status | In `D5/`, Blueprint, Evidence, Library, Papers, and Chronicle, regex-recognized handwritten English/Chinese status badges are rejected (`RepositoryRules.Structure.cs:123`). | Yes: active-rule `badge` mutation passed. | Handwritten lifecycle/status claims in recognized forms. |
| SL-011 Controlled domains | D5 formal and Blueprint/Evidence stratum paths must use a registered domain at its registered stratum (`RepositoryRules.Structure.cs:208`). | Yes: active-rule `domain` mutation passed. | Directory/domain vocabulary copied outside `Meta/domains.yaml`. |
| SL-012 Six-line Lean header | Every D5 Lean file must start with the exact six-line machine header; a unique parseable header GID must equal the path-derived GID (`RepositoryRules.Structure.cs:257`). | Yes: active-rule `header` mutation and the `missing-six-line-header` golden case passed. | Hand-copied or missing formal GID/header metadata. Duplicate GIDs are separately rejected by SL-015. |
| SL-013 Permanent task ledger | Parsed `TASK D5-Tnnnn` codes must be well-formed and unique; baseline task codes cannot disappear and recorded autopsy text cannot be shortened (`RepositoryRules.Structure.cs:288`). | Yes: active-rule `task` mutation passed. | Duplicated task identifiers and mutable hand-maintained task history, not arbitrary appearances of a case string. |
| SL-015 Machine fields and GID grammar | Repository path policy, GID character set, duplicate GIDs, evidence-kind collisions, anchor syntax, and JSON formula grammar are checked (`RepositoryRules.Content.cs:11`). | Yes: active-rule `formula` mutation plus golden cases for duplicate/unsafe GIDs and evidence collisions passed. | Canonical address/field literals and the closed formula language, not arbitrary constants. |
| SL-016 Digestion ledger | `Meta/BACKFILL.yaml` schema, source uniqueness, byte boundaries, fingerprints, receipts, task index, target existence, and derived migration/truth status are recomputed (`BackfillInventoryRule`). | Yes: seven focused SL-016 cases passed, including handwritten status, source-span fingerprint drift, and ticket/task mismatch. | Theory-source provenance and handwritten digestion state after theory-zero. |
| SL-017 Typed anchor membership | Formal header anchors and library query targets must be canonical catalog members or valid local targets; missing/noncanonical catalog bytes fail closed (`RepositoryRules.Content.cs:194`). | Yes: unregistered literature, malformed external, and uncataloged opaque anchor fixtures. | Invented or unregistered formal references. |
| SL-018 Machine-produced values | Only `Evidence/D5/values.json` is accepted; canonical producer attestation binds input hashes, kernel/parameters/results, and projection bytes (`RepositoryRules.Content.cs:227`). | Yes: active-rule `values` mutation and focused missing-attestation/input-drift fixtures passed. | Hand-filled canonical numeric projection values, not numbers elsewhere. |
| SL-014 Toolchain upgrade compatibility | Deferred under `D5-T0010`; it emits a deferred case, not a rejection predicate (`RuleCatalog.cs:196`). | No active red fixture; the deferred-state test passed. | **No active broad toolchain/version guard.** The new SDK policy above closes only one narrow copy shape. |

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
  red/green fixture proves; current-tree `emit-check` remains mandatory and byte-exact.
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

## Residual scan

| Family | Concrete instances | Existing guard | Verdict |
|---|---|---|---|
| Magic numbers and thresholds | `LeanCacheProvisioner.cs:34,47,72` repeats 1800 seconds; `RepositoryRules.Structure.cs:73-94` embeds 600/800/12 policy thresholds; `QuestPdfWriter.cs:31-47` embeds layout values 36/10/19/18/8. | BannedApi checks ambient APIs, not numeric literals. SL-018 covers only the canonical values projection. | `HC-OPEN-001`: no general low-false-positive predicate. The same syntax represents timeout policy, UI design tokens, proof constants, array bounds, and protocol widths. |
| Exact repeated string constants | Zero hash at `FrozenLedgerGenesisValidation.cs:8` and `FrozenLedgerCanonicalWriter.cs:224`; corpus schema at `GoldenCorpusMaterializer.cs:47` and `ConservativeCorpusEvaluator.cs:11`; anchor path at `CanonicalAnchorCatalogWriter.cs:9` and `AnchorCatalogLoader.cs:20`; CamelCase regex in four coordinate files. | RepositoryPathLiteral permits every const definition and does not check global uniqueness. Codec tests catch some drift after the fact. | `HC-OPEN-002`: an exact duplicate-existing-path const predicate is feasible, but choosing the canonical owner crosses assemblies and conservative C0 sources. Track as a larger consolidation unit. Arbitrary repeated strings remain high-noise. |
| Inline JSON/YAML literals | Golden base-fixture defaults in `GoldenCorpus.cs`, materializer setup, and negative fixtures in `RuleFixture.cs`. The 110 golden case declarations themselves have moved to canonical TOML and are guarded by the storage policy above. | Structured canonical writers validate admitted repository artifacts, not arbitrary C# fixture literals. | `HC-OPEN-003`: malformed-input tests must preserve noncanonical bytes; replacing them with serializers would erase the behavior under test. A global ban would mostly reject valid negative fixtures. |
| Environment, path, OS, locale | Fixed tool PATH in `Meta/StrataLint/scripts/local-harness-gate.sh:19`; POSIX `/tmp` in `WorktreeCommandTests.cs:27-82`; `/usr/bin/false` at `FaultInjectionTests.cs:106`; CLI GUID workspace suffixes at `ConservativeReplayWorkspace.cs:38` and `ConservativeExtensionCommand.cs:429,484`. The providerless CLI parse found at `RegistryLoader.cs:137` is now fixed and guarded. | Shell scripts explicitly target Bash; BannedApi now covers culture and ambient time/entropy in all production projects, but not GUID creation in CLI. No declared OS support matrix is machine checked. | `HC-OPEN-004`: without a support contract or a typed temporary-workspace capability, the machine cannot distinguish an intentional POSIX/ephemeral identifier from an accidental portability or output-determinism bug. |
| Time/tool/version literals | Production harness discovery now derives MSBuild `TargetPath`; only `Directory.Build.props`, generated lock keys, and the explicit `net99.0` analyzer fixture retain TFM text. Test-only Lean 4.24 fixture strings still differ from the live 4.31 pin. | Target-framework, SDK-workflow, central package-version, and analyzer lock-key policies cover their narrow authorities. SL-014 remains deferred. | `HC-OPEN-005` narrowed: the copied TFM subcase is closed and guarded. Test fixture tool versions remain open because equality to the live pin would erase compatibility-test intent; classify those fixtures before deriving or retaining them. |
| Test snapshots and structural assumptions | Workflow slicing by literal job names at `ReviewRegressionTests.cs:437-439`; CI shell implementation asserted by substrings at `BannedApiCoverageTests.cs:107-119`; duplicated BACKFILL projection snippets at `ReviewRegressionTests.cs:162-167` and `ProductionEnvironmentTests.cs:424-429`. | These tests detect current drift but no guard classifies which assertions are contractual versus brittle implementation snapshots. | `HC-OPEN-006`: snapshot bytes are sometimes the contract. A ban on string assertions or raw fixtures has an unacceptable false-positive rate; typed parsing must be introduced case by case. |
| csproj/props repetition | The same test SDK/xUnit bundle appears in `StrataLint.Tests.csproj:12-17`, `StrataLint.Scribe.Tests.csproj:11-16`, and `StrataLint.ArchitectureTests.csproj:15-21`. | Central package management prevents per-project version copies, but item-group duplication is allowed. | `HC-OPEN-007`: the exact three-project bundle can be centralized in evaluated MSBuild targets, but a generic duplicate-item predicate cannot know project-specific asset metadata. Treat as a scoped build refactor with lock-file verification. |
| Workflow repeated configuration | Five checkout blocks at `.github/workflows/ci.yml:27,131,158,267,275`; job timeouts at lines 24,126,251,264. | The new SDK guard covers only setup-dotnet version authority. Existing tests check trust topology by substrings. | `HC-OPEN-008`: GitHub Actions repetition can be factored only through composite/reusable workflow boundaries that alter checkout context and the base-controlled trust topology. Textual duplication alone is not a safe predicate. |
| Internal theory references outside managed sources | `docs/develop/theory/` and ingestion/status code intentionally retain the reference inputs and provenance vocabulary. | TheoryIsolation scans Lean, non-ingestion C#, and the generated catalog, not all prose/scripts/config. SL-016 governs ingestion receipts. | Guarded where references could become formal/program authority; intentionally open as reference data. "No theory token anywhere" would delete the source being digested. |
| Encoded, split, interpolated, or computed duplication | Examples can be manufactured as concatenation, base64, hash lookup, arithmetic, generated code, or runtime I/O. | Current policies deliberately match closed syntax shapes. | `HC-OPEN-009`: deciding arbitrary semantic equivalence or whether a computed value has the wrong authority reduces to program/intent equivalence. Every finite text rule has trivial encoding escapes; broadening it produces both bypasses and false positives. |
| Values schema epoch transition | Expand admitted attestation v1 or v2; migrate moved the canonical writer and artifact to v2; contract completed in this PR by removing v1 read support and retaining v1 only as an SL-018 negative fixture (expand-migrate-contract, CLAUDE.md section 6). | The conservative verifier observes a finite base-owned corpus plus the actual trees, not every historically admitted snapshot. | `VALUES-SCHEMA-EPOCH` (open): the active schema epoch/domain is not yet machine-defined, so a later v1 contract can be corpus-conservative without proving the literal universal conservative-extension law. |
| Data residence epoch | `Meta/StrataLint/Golden/cases/{digestion-and-anchors,protected-semantics,structure-and-identities,structured-ledger}.toml` and `Meta/StrataLint/Golden/values-kernels.toml` are the five known `kind=data` violations. C0 certificate and frozen events share the future relocation batch but are `kind=ledger`, not residence violations. | FILEMAP marks the two matching entries `residence_violation=true`, records count 5 and case `RESIDENCE-EPOCH`, and the repository test asserts the expanded path set equals the literal known inventory. SL-022 continues to protect Golden and `Blueprint/**/*.scribe.cs`; `CONTRACT-EPOCH` P0 now supplies the predecessor-owned obligation comparator. | `RESIDENCE-EPOCH` (P1 registered; P2 open): `RESIDENCE-EPOCH-GOLDEN-CASES-V1` and `RESIDENCE-EPOCH-VALUES-KERNELS-V1` bind the exact five paths, loader custodians, base tree, and target policy root with authority `none`. A later base-owned consumption migrates the files and renews their FILEMAP/C0 custody without widening scope or replaying either plan. |
| Bootstrap protected-surface representation | `BootstrapGate.cs:138-166` keeps the trust-root path classification and the retired Definitions prefix exception in executable code. External data would make review and generation easier, but would also make the policy that decides what is protected depend on another mutable artifact. | SL-022 and `TrustTopologyTests` exercise the in-process predicate; `DefinitionsRetirementTests` forbids the exempt directory from returning. The v1 predecessor codec still validates candidate diagnostics with its own predicate. | `HC-OPEN-010`: keep the protection surface embedded until an external representation can be content-addressed by a higher trust layer. Remove the retired-prefix exception only after a predecessor codec admits candidate-added protection; doing both in one PR currently fails closed before conservative comparison. |
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
| `StrataLint.Engine/Rules/ValuesProjectionLoader.cs:25-43,89` and `StrataLint.Scribe/Writers/CanonicalValuesWriter.cs:45` | These constants bind the D5 values pipeline specifically: D5 Lean truth, D5 kernel data, and the D5 evidence projection. The constant ID set itself lives only in emitter data. A future theory needs its own admitted source before sharing this path. |
| `StrataLint.Cli/Conservative/GoldenCorpusMaterializer.cs:272-622`, `StrataLint.Tests/Rules/RuleFixture.cs`, `StrataLint.Cli/Golden/GoldenCorpus.cs`, and `Meta/StrataLint/Golden/cases/*.toml` | The conservative corpus is an explicit synthetic fixture for the sole instantiated M0 theory. Those D5 examples remain valid fixtures after another theory is admitted. |
| `Blueprint/D5/**/*.scribe.cs` and `StrataLint.Scribe.Tests/**/*.cs` | These are typed D5 document data and tests of those documents, not a generic theory registry. |
| `StrataLint.Engine/Rules/RuleCatalog.cs:194-196`, `StrataLint.Cli/Commands/CliApplication.cs:120-124`, and `StrataLint.ArchitectureTests/CanonicalSources/TheoryIsolationPolicy.cs:19` | These literals cite permanent D5 task cases or the current D5 ingestion/autopsy grammar. The case identities must not be generalized or renumbered. |

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
| `StrataLint.Engine/Rules/RepositoryRules.cs:30,39,43`, `Coordinates/DomainTypes.cs:135`, and `Rules/Backfill/BackfillInventoryRule.cs:11,15,283` | Task, query, case, and frontier discovery implement D5-shaped identifiers instead of the `THEORY-T/Q` grammar. |
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

## CONTRACT-EPOCH (P0 complete, 2026-07-16)

This case installs obligation accounting without granting a contraction capability.
The three phases are deliberately separated across commits and consumers.

| Phase | Status | Machine boundary and close condition |
|---|---|---|
| P0 mechanism | **complete** | Protection matchers plus active-rule descriptors have a canonical policy root. The exact-base comparator loads the closed `events.jsonl`/content-addressed evidence store from both frozen commits, accepts only the sealed transfer/discharge union, computes complete retirement atoms and `uncovered_obligations`, separates candidate registration evidence from base consumption evidence, enforces one-shot append-only consumption, and rejects authority-ceiling targets. Six base-owned attack cases renew the C0 corpus. No plan is registered in this phase. |
| P1 registration | **RESIDENCE registered; E3 open** | `RESIDENCE-EPOCH` registers two exact, root-bound loader-custody plans for its five paths; candidate receipts validate but have authority `none` in this comparison. Its first real store instance exposed two P0 bootstrap gaps: inline test-path copies were centralized under one test-fixture const, and the three exact ledger/evidence artifacts were registered in the candidate registry so the base path-policy closed world remains intact. `DIGESTION-LEDGER-EPOCH` E3 still owes its separate registration. |
| P2 consumption | **not part of P0** | Each consumer may append one consume event only after its plan is present and pending in the exact base. Coverage trusts only base receipts, validates candidate custodians, requires exact delta scope and an empty uncovered set, and leaves no reusable exception. See the RESIDENCE row above and E3 below. |

P0 is a pure conservative verifier extension. There is intentionally no
`Meta/contract-epoch/` data instance in this change; the first such instance belongs to
P1 and must itself pass the P0 base judge.

### P0 verification and C0 renewal prerequisites

- P0 mechanism commit: `97658851df49cf1ec3fcc72df75a36ee25881a67`.
- Release build completed with zero warnings and zero errors; the main test assembly
  passed 631/631, and ArchitectureTests passed 121/121 when excluding only
  `TowerC0AddressesMatchTheCanonicalWorktreeBytes`, whose expected 36 source addresses
  still pointed at the predecessor's 26-member ceremony.
- The first direct ceremony admission then found that A19 had shifted all twelve
  `atomizer: none` specification receipts. `make ingest` failed closed before writing,
  as designed for manually delimited receipts with existing CAS refs. Every registered
  CAS blob occurred exactly once and the contiguous range moved by 2,024 bytes from
  `30191..33922` to `32215..35946`; fingerprints and CAS refs remain unchanged.
- The next replay reached the new exact-commit store and exposed a TOWER edge that had
  been dangling since `67f284d`: `anchor-reference-rule` named the nonexistent judge
  `golden-compatibility`. A repository-bound test failed with that sole finding before
  the edge was corrected to the existing `golden-corpus` machine component; the focused
  test then passed 1/1.
- Deterministic selftest passed. This prerequisite commit grants no plan and changes no
  policy atom; a following docs-only successor binds its exact base as the protected
  preimage for the C0 renewal.
- The first closed-graph comparator attempt used base
  `86acea53c3da0eaebc03c3ef52847cd4396f0602` and docs-only preimage
  `3d95fee18a7eebd7399ee6627353ac708da4ea3f`. It reached C0 actual validation and found
  that later renewals had path-sorted the 26 evidence records, while the original
  `0034d82` ceremony and `HasCanonicalC0Ceremony` require complete-record ordinal order.
  A repository-bound test failed with the sole `TOWER-C0-CEREMONY` finding; byte-exact
  reordering made both `sort -c` and the focused test pass. This correction commit will
  be the next comparator base, with a separate docs-only protected preimage.
- Canonical C0 comparator base commit: `1834a05f1539e65481d9d510022630bfe13fdbca`.
- This docs-only successor is the protected preimage for that base-owned renewal. It
  grants no plan and changes no policy atom.
- The emitted certificate binds preimage `a25b021fefeaced4409e913917993b452503bd01`
  and tree `e0e0f838a1ae6868689f658915ab5cc08bcb76cb`, with SHA-256
  `60ec1a84c5baec83164ae040e684327b4e519cd19347be20f8ee5d2543b37f2a`.
  It records zero findings, 117 golden cases, six contract attacks, 37/37 preserved
  admits, equal pre/post policy roots, and no retired or uncovered obligations. TOWER
  now carries the complete 36-record ceremony in canonical ordinal order.

## DIGESTION-LEDGER-EPOCH (active, 2026-07-15)

This epoch moves digestion preimages from mutable theory volumes into a replayable
content-addressed ledger without weakening an already admitted path. Its stages are
deliberately split so the expand judge remains conservative and the later contract pays
for its protection-surface change explicitly.

| Segment | Status | Machine boundary and close condition |
|---|---|---|
| E1 expand | **complete** | Schema 3 accepts optional `cas_ref`; canonical raw bytes live at `Meta/Digestion/atoms/sha256/<64-lower-hex>`. The judge verifies ref/path/blob/raw-fingerprint equality plus missing, corrupt, and orphan blobs. A CAS-backed receipt no longer needs volume reconciliation; a receipt without `cas_ref` follows the unchanged #109 path. Theory and CAS bytes may be opaque, ingest writes CAS refs, and source-format failure produces one reported whole-source coarse atom once that source's existing receipts are CAS-backed. I/O, schema, CAS, hash, and atomizer-integrity failures still block. The CAS object directory is outside SL-003 code-bucket capacity but only for canonical addresses. |
| E2 migrate | **complete** | All 789 current GICT/PZG receipts (81 GICT, 708 PZG, including 769 residual-open) and all 12 `atomizer: none` specification receipts now bind exact raw CAS bytes through `cas_ref`. The specification receipts retain their 12 byte boundaries and source reconciliation for `SPEC-ZERO-ANCHOR`; no reader is contracted here. The canonical stock test requires every current receipt preimage and the CAS judge proves zero orphan, dangling, or hash-mismatched objects. A repeated `make ingest BASE=origin/dev` wrote zero objects, reported `ledger_changed=false`, and preserved the ledger SHA-256 byte-for-byte. |
| E-verifier | **P0 complete** | `CONTRACT-EPOCH` now provides the exact-base policy delta, sealed plan, one-shot ledger, content-addressed receipt, authority ceiling, and uncovered-obligation comparator. It grants no declaration by itself; E3 still owes its own P1 registration and P2 consumption. |
| E3 contract | **pending** | Only after E2, the E3-specific P1 plan, and the separate specification-receipt case close, consume that plan once to remove the boundary/stale/source-content/atomizer admission readers, make theory a non-bearing reference class, and remove transitional schema fields in one certificate-bearing contract change. |

E1 changes no canonical `Meta/BACKFILL.yaml` entry and no golden corpus case, so it needs
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

## DIGESTION-PHASE2-INGEST (complete, 2026-07-15)

After PR #109 supplied cross-syntax receipt identity and one-step legacy conversion,
`make ingest` completed the Phase 2 extract→identify→subtract→residual pass for the
PR #106 theory volumes. It migrated all 20 atomized legacy receipts from `boundary` to
`ast_path` (GICT 16, PZG 4), while leaving the 12 `atomizer: none` specification
receipts unchanged. The resulting alignment and ledger write recorded:

- seen: 15
- stale acknowledged: 5 (`gict-hearts-o5-o6`, `gict-constant-Cphi`,
  `gict-constant-T0`, `gict-constant-delta-mean`, `gict-constant-c1`)
- residual-open added: 737 (GICT 55, PZG 682)
- ledger changed: true

### First-voyage autopsy (REFERENCE-ZERO-ANCHOR migrate, 2026-07-15)

`make ingest` did not reach a ledger write. With the production ledger unchanged, its
legacy byte boundaries point into the new theory bytes; the first truncated UTF-8 span
fails during digest-status evaluation. A minimal data-only trial converted only the 20
GICT/PZG receipts from `boundary` to `ast_path` and left all 12 `atomizer: none` spec
receipts untouched. That exposed the alignment counts but was also rejected by the
base-owned judge:

- seen: 15
- intended stale: 5 (`gict-hearts-o5-o6`, `gict-constant-Cphi`,
  `gict-constant-T0`, `gict-constant-delta-mean`, `gict-constant-c1`)
- reported residual-open frontier: 737

The count is 737 rather than the expected version delta of about 165 because the
aligner subtracts only registered receipt paths, not the 587 claims atomized from the
baseline theory volumes. More importantly, stale admission requires the candidate
receipt preimage to be byte-equal to `origin/dev`; a structured `ast_path` receipt
cannot be byte-equal to its legacy `boundary` preimage. The second `make ingest`
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
