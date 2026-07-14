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
| Repository path literal policy | All tracked C# string literals are checked. A value with at least two `/` characters that exactly names an existing file is rejected unless it directly defines a `const string` (`RepositoryPathLiteralPolicy.cs:22`). | Yes: `ExistingMultisegmentPathLiteralIsRejectedByTheRedFixture`; green const and nonexistent-path counterfixtures also passed. | Consumers copying existing repository file paths. |
| Default injection policy | Effectively public members on effectively public `*Dsl` or `*Builder` types may not use a literal GID, case ID, or canonical anchor as a parameter default (`DefaultInjectionPolicy.cs:20`). | Yes: `CanonicalLiteralDefaultIsRejectedByTheRedFixture`; GID and case variants passed. | Hidden canonical policy injected through public defaults. |
| Theory isolation, sources | All Lean and all non-ingestion C# reject internal theory paths and the retired theory-family tokens; Lean task autopsy text and the ingestion whitelist are explicit exceptions (`TheoryIsolationPolicy.cs:46,76`). | Yes: Lean header, non-autopsy task, and C# citation negative fixtures passed. | Formal/program code coupled to internal theory reference sources or numbering families. |
| Theory isolation, generated catalog | Parsed generated anchor definitions reject retired internal theory schemes (`TheoryIsolationPolicy.cs:104`). | Yes: `CatalogTheorySchemeIsRejectedByTheRedFixture` passed. | Generated catalog reintroducing internal theory schemes. |
| External anchor catalog consistency | Typed catalog entries must be external literature/mathlib anchors, exactly equal the external manifest, with property names derived from the anchor (`AnchorCatalogConsistencyTests.cs:8`). | Yes for name transform: `MismatchedExternalAnchorPropertyNameIsRejectedByTheRedFixture`; repository equality checks are live tripwires. | Hand-copied anchor identity and drift between manifest and typed catalog. |
| C0 ceremony trust root | Recursive controller/corpus/gate source sets, Git blob OIDs, certificate SHA-256, preimage commit/tree, and implication counts must match live bytes (`C0CeremonyTrustRootTests.cs:68`). | Partial: recursive-discovery synthetic fixtures exist; byte/address mismatch has no isolated synthetic fixture. The repository-bound tripwire passed. | Unattested changes to the conservative-extension controller, corpus, gate wiring, or inaugural certificate. |
| Central package version literal policy | Every tracked C# string literal exactly equal to a `Directory.Packages.props` version is rejected; an empty/malformed central version set fails closed (`CentralPackageVersionLiteralPolicy.cs:15,28,43`). | Yes: copied-version and empty-catalog red fixtures; the real `5.6.0` copy failed before stock repair. | Exact C# copies of central NuGet versions. |
| .NET SDK single-source policy | Every parsed `.github/workflows/*.{yml,yaml}` `actions/setup-dotnet@*` step (case-insensitive action identity) must use `global-json-file` and must not contain `dotnet-version`; the canonical CI workflow must contain both candidate/baseline global-json references (`DotnetSdkSingleSourcePolicy.cs:9`). | Yes: mixed-case copied-version, additional-workflow copied-version, and missing-baseline red fixtures; both real workflow copies failed before repair. | Workflow copies or ambient omission of the SDK version pinned by `global.json`. |
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

## Residual scan

| Family | Concrete instances | Existing guard | Verdict |
|---|---|---|---|
| Magic numbers and thresholds | `LeanCacheProvisioner.cs:34,47,72` repeats 1800 seconds; `RepositoryRules.Structure.cs:73-94` embeds 600/800/12 policy thresholds; `QuestPdfWriter.cs:31-47` embeds layout values 36/10/19/18/8. | BannedApi checks ambient APIs, not numeric literals. SL-018 covers only the canonical values projection. | `HC-OPEN-001`: no general low-false-positive predicate. The same syntax represents timeout policy, UI design tokens, proof constants, array bounds, and protocol widths. |
| Exact repeated string constants | Zero hash at `FrozenLedgerGenesisValidation.cs:8` and `FrozenLedgerCanonicalWriter.cs:224`; corpus schema at `GoldenCorpusMaterializer.cs:47` and `ConservativeCorpusEvaluator.cs:11`; anchor path at `CanonicalAnchorCatalogWriter.cs:9` and `AnchorCatalogLoader.cs:20`; CamelCase regex in four coordinate files. | RepositoryPathLiteral permits every const definition and does not check global uniqueness. Codec tests catch some drift after the fact. | `HC-OPEN-002`: an exact duplicate-existing-path const predicate is feasible, but choosing the canonical owner crosses assemblies and conservative C0 sources. Track as a larger consolidation unit. Arbitrary repeated strings remain high-noise. |
| Inline JSON/YAML literals | Golden base-fixture defaults in `GoldenCorpus.cs`, materializer setup, and negative fixtures in `RuleFixture.cs`. The 110 golden case declarations themselves have moved to canonical TOML and are guarded by the storage policy above. | Structured canonical writers validate admitted repository artifacts, not arbitrary C# fixture literals. | `HC-OPEN-003`: malformed-input tests must preserve noncanonical bytes; replacing them with serializers would erase the behavior under test. A global ban would mostly reject valid negative fixtures. |
| Environment, path, OS, locale | Fixed tool PATH in `Meta/StrataLint/scripts/local-harness-gate.sh:19`; POSIX `/tmp` in `WorktreeCommandTests.cs:27-82`; `/usr/bin/false` at `FaultInjectionTests.cs:106`; CLI GUID workspace suffixes at `ConservativeReplayWorkspace.cs:38` and `ConservativeExtensionCommand.cs:429,484`. The providerless CLI parse found at `RegistryLoader.cs:137` is now fixed and guarded. | Shell scripts explicitly target Bash; BannedApi now covers culture and ambient time/entropy in all production projects, but not GUID creation in CLI. No declared OS support matrix is machine checked. | `HC-OPEN-004`: without a support contract or a typed temporary-workspace capability, the machine cannot distinguish an intentional POSIX/ephemeral identifier from an accidental portability or output-determinism bug. |
| Time/tool/version literals | Remaining copied target framework in `.github/scripts/harness-gate.sh:42`, `ConservativeExtensionCommand.cs:304`, and its test setup at `ConservativeHarnessProgramTests.cs:18,26`; test-only Lean 4.24 fixture strings differ from the live 4.31 pin. | SDK workflow copies, central package-version copies, and analyzer lock framework lookup are now guarded/derived. SL-014 remains deferred. | `HC-OPEN-005`: exact `net10.0` copies are judgeable, but the production consumers are in the C0/gate trust surface; repair requires deriving `TargetPath` and renewing the C0 ceremony, so it is a larger work item. Test fixture versions need intent, not equality to the live pin. |
| Test snapshots and structural assumptions | Workflow slicing by literal job names at `ReviewRegressionTests.cs:437-439`; CI shell implementation asserted by substrings at `BannedApiCoverageTests.cs:107-119`; duplicated BACKFILL projection snippets at `ReviewRegressionTests.cs:162-167` and `ProductionEnvironmentTests.cs:424-429`. | These tests detect current drift but no guard classifies which assertions are contractual versus brittle implementation snapshots. | `HC-OPEN-006`: snapshot bytes are sometimes the contract. A ban on string assertions or raw fixtures has an unacceptable false-positive rate; typed parsing must be introduced case by case. |
| csproj/props repetition | The same test SDK/xUnit bundle appears in `StrataLint.Tests.csproj:12-17`, `StrataLint.Scribe.Tests.csproj:11-16`, and `StrataLint.ArchitectureTests.csproj:15-21`. | Central package management prevents per-project version copies, but item-group duplication is allowed. | `HC-OPEN-007`: the exact three-project bundle can be centralized in evaluated MSBuild targets, but a generic duplicate-item predicate cannot know project-specific asset metadata. Treat as a scoped build refactor with lock-file verification. |
| Workflow repeated configuration | Five checkout blocks at `.github/workflows/ci.yml:27,131,158,267,275`; job timeouts at lines 24,126,251,264. | The new SDK guard covers only setup-dotnet version authority. Existing tests check trust topology by substrings. | `HC-OPEN-008`: GitHub Actions repetition can be factored only through composite/reusable workflow boundaries that alter checkout context and the base-controlled trust topology. Textual duplication alone is not a safe predicate. |
| Internal theory references outside managed sources | `docs/develop/theory/` and ingestion/status code intentionally retain the reference inputs and provenance vocabulary. | TheoryIsolation scans Lean, non-ingestion C#, and the generated catalog, not all prose/scripts/config. SL-016 governs ingestion receipts. | Guarded where references could become formal/program authority; intentionally open as reference data. "No theory token anywhere" would delete the source being digested. |
| Encoded, split, interpolated, or computed duplication | Examples can be manufactured as concatenation, base64, hash lookup, arithmetic, generated code, or runtime I/O. | Current policies deliberately match closed syntax shapes. | `HC-OPEN-009`: deciding arbitrary semantic equivalence or whether a computed value has the wrong authority reduces to program/intent equivalence. Every finite text rule has trivial encoding escapes; broadening it produces both bypasses and false positives. |
| Values schema epoch transition | Expand admitted attestation v1 or v2; migrate moved the canonical writer and artifact to v2; contract completed in this PR by removing v1 read support and retaining v1 only as an SL-018 negative fixture (expand-migrate-contract, CLAUDE.md section 6). | The conservative verifier observes a finite base-owned corpus plus the actual trees, not every historically admitted snapshot. | `VALUES-SCHEMA-EPOCH` (open): the active schema epoch/domain is not yet machine-defined, so a later v1 contract can be corpus-conservative without proving the literal universal conservative-extension law. |
| Bootstrap protected-surface representation | `BootstrapGate.cs:138-169` keeps the trust-root path classification in executable code. External data would make review and generation easier, but would also make the policy that decides what is protected depend on another mutable artifact. | SL-022 and `TrustTopologyTests` exercise the current in-process predicate; there is no higher-level signed loader/schema for an external policy. | `HC-OPEN-010`: keep the protection surface embedded until an external representation can be content-addressed and validated by a strictly higher trust layer. Moving the list now would relocate, not remove, the trust root. |
| Diagnostic language consistency | English route/parser failures coexist with Chinese SL-021 and bootstrap messages (`Routing.cs:80,85`; `RepositoryRules.Admission.cs:77,82`; `CliApplication.cs:120,124`). Atomizer diagnostics added in this unit are English. | No diagnostic locale/style schema exists; golden cases intentionally bind some current bytes. | `HC-OPEN-011`: terminology and locale are user-interface policy, not a correctness literal. Standardize only with a declared diagnostic style plus an atomic golden-corpus migration; do not mix that migration into registry work. |

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
| `StrataLint.Engine/Rules/ValuesProjectionLoader.cs:25-48,95,277-283` and `StrataLint.Scribe/Writers/CanonicalValuesWriter.cs:45` | These constants bind the D5 values pipeline specifically: D5 Lean truth, D5 kernel data, and the D5 evidence projection. A future theory needs its own admitted source before sharing this path. |
| `StrataLint.Cli/Conservative/GoldenCorpusMaterializer.cs:272-622`, `StrataLint.Tests/Rules/RuleFixture.cs`, `StrataLint.Definitions/Golden/GoldenCorpus.cs`, and `Meta/StrataLint/Golden/cases/*.toml` | The conservative corpus is an explicit synthetic fixture for the sole instantiated M0 theory. Those D5 examples remain valid fixtures after another theory is admitted. |
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
