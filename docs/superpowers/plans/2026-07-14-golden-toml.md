# Golden TOML Corpus Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace all 110 C# golden case declarations with a strict canonical TOML corpus, add machine recording, and renew the Component C trust root without changing any case behavior.

**Architecture:** Definitions owns the closed schema plus Tomlyn loader/canonical writer. A single CLI-side golden executor applies mutations and feeds both Engine checks and Component C materialization; a CLI record command uses that same executor to rewrite diagnostic snapshots. Architecture tests guard the data/program boundary and the closed stratum alphabet.

**Tech Stack:** .NET 10, C# 14, Tomlyn 2.10.1, xUnit, existing StrataLint Engine and conservative-extension harness.

---

### Task 1: Capture The Typed Baseline

**Files:**
- Create temporarily: `.golden-migration/GoldenMigration.csproj`
- Create temporarily: `.golden-migration/Program.cs`
- Produce: caller scratch `typed-baseline.json`

- [ ] **Step 1: Add a reflection-only baseline exporter**

The temporary program loads `StrataLint.Definitions.GoldenCorpus.All` and
`StrataLint.Cli.GoldenCorpusMaterializer.Materialize`, then emits sorted objects
with `name`, rendered expected diagnostics, and the materialized `case_root`.

```csharp
using System.Collections;
using System.Reflection;
using System.Text;
using System.Text.Json;
using StrataLint.Definitions;

var repositoryRoot = Path.GetFullPath(args[0]);
var outputPath = Path.GetFullPath(args[1]);
var definitions = typeof(StrataLint.Definitions.Anchor).Assembly;
var corpusType = definitions.GetType("StrataLint.Definitions.GoldenCorpus", true)!;
var all = (System.Collections.IEnumerable)corpusType
    .GetProperty("All", BindingFlags.Static | BindingFlags.NonPublic)!.GetValue(null)!;
var expectations = all.Cast<object>().ToDictionary(
    item => (string)item.GetType().GetProperty("Name")!.GetValue(item)!,
    item => ((IEnumerable)item.GetType().GetProperty("ExpectedDiagnostics")!.GetValue(item)!)
        .Cast<object>()
        .Select(diagnostic =>
            $"SL-{(int)diagnostic.GetType().GetProperty("RuleNumber")!.GetValue(diagnostic)!:000} "
            + $"{diagnostic.GetType().GetProperty("Path")!.GetValue(diagnostic)}: "
            + diagnostic.GetType().GetProperty("Message")!.GetValue(diagnostic))
        .Order(StringComparer.Ordinal)
        .ToArray(),
    StringComparer.Ordinal);
var materializer = typeof(StrataLint.Cli.Program).Assembly
    .GetType("StrataLint.Cli.GoldenCorpusMaterializer", true)!;
var materialized = materializer.GetMethod(
    "Materialize",
    BindingFlags.Static | BindingFlags.NonPublic)!.Invoke(null, [repositoryRoot])!;
var bytes = ((IEnumerable)materialized.GetType()
    .GetProperty("CanonicalBytes")!.GetValue(materialized)!).Cast<byte>().ToArray();
using var document = JsonDocument.Parse(bytes);
var roots = document.RootElement.GetProperty("cases").EnumerateArray().ToDictionary(
    item => item.GetProperty("case_id").GetString()!["golden:".Length..],
    item => item.GetProperty("case_root").GetString()!,
    StringComparer.Ordinal);
var cases = expectations.OrderBy(static item => item.Key, StringComparer.Ordinal).Select(item => new
{
    name = item.Key,
    diagnostics = item.Value,
    case_root = roots[item.Key],
});
var json = JsonSerializer.SerializeToUtf8Bytes(new
{
    corpus_root = (string)materialized.GetType().GetProperty("Root")!.GetValue(materialized)!,
    cases,
});
File.WriteAllBytes(outputPath, [.. json, (byte)'\n']);
```

- [ ] **Step 2: Run the exporter against the untouched typed corpus**

Run: `dotnet run --project .golden-migration/GoldenMigration.csproj -- <scratch>/typed-baseline.json`

Expected: exit 0; JSON contains 110 unique cases and whole corpus root
`sha256:ff87ba121233899d9bedf80471e71248523cedeb60c34105de5839b5b4c533e7`.

- [ ] **Step 3: Preserve the artifact outside git and remove the temporary project**

Run: `git status --short`

Expected: no `.golden-migration` paths remain.

### Task 2: Drive The Strict Loader From Red Tests

**Files:**
- Create: `Meta/StrataLint/StrataLint.Tests/Golden/Fixtures/valid.toml`
- Create: `Meta/StrataLint/StrataLint.Tests/Golden/Fixtures/unknown-key.toml`
- Create: `Meta/StrataLint/StrataLint.Tests/Golden/Fixtures/unknown-op.toml`
- Create: `Meta/StrataLint/StrataLint.Tests/Golden/Fixtures/wrong-type.toml`
- Create: `Meta/StrataLint/StrataLint.Tests/Golden/TomlGoldenLoaderTests.cs`
- Modify: `Directory.Packages.props`
- Modify: `Meta/StrataLint/StrataLint.Definitions/StrataLint.Definitions.csproj`

- [ ] **Step 1: Write one green-shape test and three fail-closed fixture tests**

```csharp
[Fact]
public void CanonicalFixtureLoads() =>
    Assert.Equal("valid", Assert.Single(TomlGoldenLoader.LoadFile(Fixture("valid.toml"))).Name);

[Theory]
[InlineData("unknown-key.toml", "unknown key")]
[InlineData("unknown-op.toml", "unknown golden mutation op")]
[InlineData("wrong-type.toml", "must be an integer")]
public void InvalidFixtureFailsClosed(string file, string message) =>
    Assert.Contains(message, Assert.Throws<FormatException>(
        () => TomlGoldenLoader.LoadFile(Fixture(file))).Message, StringComparison.Ordinal);
```

- [ ] **Step 2: Run the focused tests and observe RED**

Run: `dotnet test Meta/StrataLint/StrataLint.Tests/StrataLint.Tests.csproj -c Release --filter FullyQualifiedName~TomlGoldenLoaderTests`

Expected: compile failure because `TomlGoldenLoader` does not exist.

- [ ] **Step 3: Pin and reference Tomlyn 2.10.1**

Add `<PackageVersion Include="Tomlyn" Version="2.10.1" />` centrally and
`<PackageReference Include="Tomlyn" />` only to Definitions, then restore with
`dotnet restore Meta/StrataLint/StrataLint.sln --force-evaluate` so every lock
file reflects the transitive runtime dependency.

### Task 3: Implement Schema, Loader, And Canonical Writer

**Files:**
- Modify: `Meta/StrataLint/StrataLint.Definitions/Golden/GoldenCorpus.cs`
- Create: `Meta/StrataLint/StrataLint.Definitions/Golden/TomlGoldenLoader.cs`
- Create: `Meta/StrataLint/StrataLint.Definitions/Golden/TomlGoldenWriter.cs`

- [ ] **Step 1: Add loader-facing schema without breaking the legacy exporter**

Keep `GoldenCase`, `GoldenDiagnostic`, `GoldenGenerality`, `GoldenStratum`, and
the 13-record `GoldenMutation` union unchanged. Temporarily retain `All`, the
`Corpus1`-`Corpus4` aggregation, and constructor aliases so Task 4 can export the
compiled legacy records through the new writer. They are removed only after the
recursive legacy/TOML comparison succeeds.

- [ ] **Step 2: Implement closed-world Tomlyn model decoding**

```csharp
internal static GoldenMutation ParseMutation(TomlTable table, string location)
{
    var op = RequiredString(table, "op", location);
    return op switch
    {
        "write" => new GoldenMutation.Write(
            RequiredString(table, "path", location),
            RequiredString(table, "content", location)),
        "write_parts" => new GoldenMutation.WriteParts(
            RequiredString(table, "path", location),
            RequiredStringArray(table, "parts", location)),
        "lean" => new GoldenMutation.Lean(
            RequiredString(table, "path", location),
            RequiredString(table, "raw_gid", location),
            RequiredGenerality(table, "generality", location),
            RequiredString(table, "body", location)),
        "delete" => new GoldenMutation.Delete(
            RequiredString(table, "path", location)),
        "append_lines" => new GoldenMutation.AppendLines(
            RequiredString(table, "path", location),
            RequiredInt32(table, "count", location, minimum: 0),
            RequiredString(table, "line", location)),
        "add_domain" => new GoldenMutation.AddDomain(
            RequiredString(table, "name", location),
            RequiredStratum(table, "stratum", location)),
        "add_task" => new GoldenMutation.AddTask(
            RequiredString(table, "path", location),
            RequiredString(table, "raw_gid", location),
            RequiredString(table, "raw_case_id", location)),
        "populate_directory" => new GoldenMutation.PopulateDirectory(),
        "empty_mirror_waiver" => new GoldenMutation.EmptyMirrorWaiver(),
        "evidence_mirror" => new GoldenMutation.EvidenceMirror(
            RequiredBoolean(table, "include_json", location),
            RequiredBoolean(table, "include_yaml", location)),
        "replace_backfill" => new GoldenMutation.ReplaceBackfill(
            RequiredString(table, "old_value", location),
            RequiredString(table, "new_value", location)),
        "replace_first_backfill_disposition" =>
            new GoldenMutation.ReplaceFirstBackfillDisposition(
                RequiredString(table, "raw_gid", location)),
        "mutate_backfill_anchor" => new GoldenMutation.MutateBackfillAnchor(
            RequiredString(table, "anchor", location),
            RequiredBoolean(table, "duplicate", location)),
        _ => throw Invalid(location, $"unknown golden mutation op: {op}"),
    };
}
```

For every table, compare keys with the exact required/optional set before reading
values. Read TOML integers only as `long`, booleans only as `bool`, strings only
as `string`, and arrays/tables only as Tomlyn container types. Parse
`GoldenStratum` with `Enum.TryParse(value, ignoreCase: false, out ...)`.

- [ ] **Step 3: Implement deterministic TOML emission**

Emit the two fixed header comments, `[[cases]]`, and the five case keys in the
design order. Encode every string as one TOML basic string with deterministic
escapes and terminate with one LF.

- [ ] **Step 4: Enforce canonical input bytes**

Reject BOM, invalid UTF-8, CR bytes, missing terminal LF, parse diagnostics,
noncanonical writer round trips, non-`.toml` discovery, empty directories, and
duplicate names across files.

- [ ] **Step 5: Run focused tests and observe GREEN**

Run the Task 2 test command.

Expected: 4 tests pass, 0 fail.

### Task 4: Generate And Prove The TOML Migration

**Files:**
- Create: `Meta/StrataLint/Golden/cases/structure-and-identities.toml`
- Create: `Meta/StrataLint/Golden/cases/digestion-and-anchors.toml`
- Create: `Meta/StrataLint/Golden/cases/structured-ledger.toml`
- Create: `Meta/StrataLint/Golden/cases/protected-semantics.toml`
- Delete: `Meta/StrataLint/StrataLint.Definitions/Golden/GoldenCorpus.Cases01.cs`
- Delete: `Meta/StrataLint/StrataLint.Definitions/Golden/GoldenCorpus.Cases02.cs`
- Delete: `Meta/StrataLint/StrataLint.Definitions/Golden/GoldenCorpus.Cases03.cs`
- Delete: `Meta/StrataLint/StrataLint.Definitions/Golden/GoldenCorpus.Cases04.cs`

- [ ] **Step 1: Build while legacy cases and the new writer coexist**

Run: `dotnet build Meta/StrataLint/StrataLint.Definitions/StrataLint.Definitions.csproj -c Release --warnaserror`

Expected: exit 0.

- [ ] **Step 2: Reflection-export the four private legacy arrays through the canonical writer**

Map `Corpus1` through `Corpus4` to the four domain filenames in order. Do not
hand-transcribe strings or expand operations.

- [ ] **Step 3: Load the four TOML files and compare every schema field to legacy records**

Expected: 110 names, no duplicates, and recursive equality of baseline mutations,
mutations, expected diagnostics, and changes.

- [ ] **Step 4: Delete the four case source files and remove migration-only code**

Remove `All`, `Corpus1`-`Corpus4` aggregation, and constructor aliases
`C/D/W/WP/L/X/A/Domain/T/Dir/Waiver/Mirror/Replace/Disposition/Anchor` from
`GoldenCorpus.cs`, leaving only schema and fixture defaults.

Run: `rg -n "private static GoldenCase\[\] Corpus|\bC\(" Meta/StrataLint --glob '*.cs'`

Expected: no C# case declarations.

### Task 5: Unify Check And Component C Execution

**Files:**
- Create: `Meta/StrataLint/StrataLint.Cli/Conservative/GoldenCaseExecutor.cs`
- Modify: `Meta/StrataLint/StrataLint.Cli/Conservative/GoldenCorpusMaterializer.cs`
- Modify: `Meta/StrataLint/StrataLint.Tests/Golden/GoldenCorpusTests.cs`
- Modify: `Meta/StrataLint/StrataLint.Tests/Golden/GoldenCorpusShapeTests.cs`
- Modify: `Meta/StrataLint/StrataLint.Tests/Rules/RuleFixture.cs`
- Delete: `Meta/StrataLint/StrataLint.Tests/Rules/RuleFixture.Golden.cs`
- Modify: `Meta/StrataLint/StrataLint.Tests/Conservative/GoldenCorpusMaterializerTests.cs`

- [ ] **Step 1: Change tests to request a loaded corpus and shared execution**

Golden checks load the repository TOML directory, call
`GoldenCaseExecutor.Evaluate(root, testCase)`, sort `Diagnostic.Render()`, and
compare it with the stored expected list. Materializer tests assert base-root
loading and absence of expected labels from conservative bytes.

- [ ] **Step 2: Run focused tests and observe RED**

Run: `dotnet test Meta/StrataLint/StrataLint.Tests/StrataLint.Tests.csproj -c Release --filter "FullyQualifiedName~GoldenCorpus"`

Expected: compile failure until the executor API exists.

- [ ] **Step 3: Move the existing fixture state and mutation switch into one executor**

The executor constructs current/baseline files and Lean reports, normalizes
BACKFILL targets, applies mutations once per requested state, and exposes both a
`RuleEvaluationContext` result and materializer state. Materializer delegates to
it; test-only duplicated methods are removed.

- [ ] **Step 4: Run focused tests and observe GREEN**

Expected: 110 per-case check rows plus shape and materializer tests pass.

### Task 6: Add Machine Record Mode

**Files:**
- Create: `Meta/StrataLint/StrataLint.Cli/Commands/GoldenRecordCommand.cs`
- Modify: `Meta/StrataLint/StrataLint.Cli/Commands/CliApplication.cs`
- Modify: `Meta/StrataLint/StrataLint.Cli/Admission/ProductionCliEnvironment.cs`
- Create: `Meta/StrataLint/StrataLint.Tests/Golden/GoldenRecordCommandTests.cs`
- Modify: `Meta/StrataLint/StrataLint.Tests/Admission/CliOutcomeTests.cs`
- Modify: `Meta/StrataLint/StrataLint.Tests/Commands/MakeWorkflowTests.cs`
- Modify: `Makefile`

- [ ] **Step 1: Write RED tests for record behavior**

Test that a copied canonical corpus with one wrong expectation is rewritten from
Engine output, a second record is byte-identical, no mutation/name/change field
changes, and CLI usage contains `golden-record`. Test that `make record-golden`
dispatches only to `StrataLint golden-record` and that CI text contains no record
invocation.

- [ ] **Step 2: Run record tests and observe RED**

Run: `dotnet test Meta/StrataLint/StrataLint.Tests/StrataLint.Tests.csproj -c Release --filter "FullyQualifiedName~GoldenRecordCommandTests|FullyQualifiedName~MakeWorkflowTests"`

- [ ] **Step 3: Implement local-only canonical rewrite**

Load all source files, evaluate every case, replace only each record's expected
diagnostic list, and write through `TomlGoldenWriter`. Return a count and never
stage, commit, or invoke admission.

- [ ] **Step 4: Add `record-golden` to the thin Make dispatch table**

The target invokes the already-built CLI through the same .NET entry pattern as
other author tools and appears in `make help`.

- [ ] **Step 5: Run record tests and observe GREEN**

Expected: all selected tests pass and a second real `make record-golden` makes no diff.

### Task 7: Update Architecture Guards And Documentation

**Files:**
- Create: `Meta/StrataLint/StrataLint.ArchitectureTests/CanonicalSources/GoldenCorpusStoragePolicy.cs`
- Create: `Meta/StrataLint/StrataLint.ArchitectureTests/CanonicalSources/GoldenCorpusStorageTests.cs`
- Create: `Meta/StrataLint/StrataLint.ArchitectureTests/CanonicalSources/StratumAlphabetTests.cs`
- Modify: `Meta/StrataLint/StrataLint.ArchitectureTests/Dependencies/DefinitionsLayerTests.cs`
- Modify: `Meta/StrataLint/StrataLint.ArchitectureTests/Dependencies/DependencyDirectionTests.cs`
- Modify: `Meta/StrataLint/Architecture/HARDCODE-LEDGER.md`
- Modify: `Meta/StrataLint/Architecture/MAP.md`
- Modify: `Meta/StrataLint/StrataLint.ArchitectureTests/MAP.md`
- Modify: `Meta/StrataLint/TOWER.yaml`

- [ ] **Step 1: Write RED storage and stratum anchor fixtures**

Reject synthetic `new GoldenCase(...)`/legacy corpus declarations in C#, accept
schema/loader code, and compare `{S0,S1,S2,S3,S4}` with `GoldenStratum`, Engine
`Stratum`, `RepositoryRules.IsStratum`, and `Gid.IsStratum` via reflection.

- [ ] **Step 2: Run architecture tests and observe RED**

Run: `dotnet test Meta/StrataLint/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj -c Release --filter "FullyQualifiedName~GoldenCorpusStorageTests|FullyQualifiedName~StratumAlphabetTests|FullyQualifiedName~DefinitionsLayerTests|FullyQualifiedName~DependencyDirectionTests"`

- [ ] **Step 3: Implement the narrow policy and update ownership assertions**

Definitions now explicitly permits only Tomlyn as a non-platform dependency.
Remove obsolete canonical-data rows for the four deleted case files and retain
schema ownership checks. Update the TOWER `golden-corpus` member list to TOML,
loader/writer/executor, and check tests.

- [ ] **Step 4: Update the hard-code ledger by the #96 standard action**

Name TOML as authority, record the real repaired C# stock, cite the synthetic red
fixture and green counterfixture, and state the predicate boundary: it rejects
golden case construction, not arbitrary test strings or schema records.

- [ ] **Step 5: Run architecture tests and observe GREEN**

Expected: selected and full architecture projects pass.

### Task 8: Prove Equivalence And Create The C0 Preimage

**Files:**
- Modify: `Meta/StrataLint/StrataLint.ArchitectureTests/CanonicalSources/C0CeremonyTrustRootTests.cs`
- Modify: `Meta/StrataLint/TOWER.yaml`

- [ ] **Step 1: Export the TOML projection to caller scratch**

Produce `toml-baseline.json` with the same sorted shape as Task 1.

- [ ] **Step 2: Byte-compare typed and TOML projections**

Run: `cmp <scratch>/typed-baseline.json <scratch>/toml-baseline.json`

Expected: exit 0; 110 diagnostic arrays and 110 case roots are identical, and
whole corpus root remains `sha256:ff87ba121233899d9bedf80471e71248523cedeb60c34105de5839b5b4c533e7`.

- [ ] **Step 3: Verify implementation before the preimage commit**

Run focused tests, `make dotnet`, `make test`, `make emit-check`, and
`git diff --check`.

- [ ] **Step 4: Commit the implementation preimage**

Run: `git commit -m "refactor(harness): move golden corpus to TOML"`

Do not push. Record the commit and tree OIDs.

- [ ] **Step 5: Generate a fresh conservative certificate against `origin/dev`**

Run the canonical local gate with baseline and candidate Lean reports, capture the
JSON emitted by `verify-conservative`, and require status `CORPUS_CONSERVATIVE`,
`golden_case_count = 110`, `findings = []`, and equal implication counts.

### Task 9: Renew C0 And Deliver Caller Artifacts

**Files:**
- Modify: `Meta/StrataLint/Golden/c0-inaugural-conservative-certificate.json`
- Modify: `Meta/StrataLint/TOWER.yaml`
- Write outside git: caller `result.json`
- Write outside git: caller `log.md`
- Write outside git: caller `done.sentinel`

- [ ] **Step 1: Install the canonical certificate bytes**

Use the emitted JSON as one canonical LF-terminated line. Update TOWER records for
all discovered controller/corpus/gate blobs, base commit, certificate SHA-256,
implementation preimage commit, and preimage tree.

- [ ] **Step 2: Run fresh completion verification**

Run `make dotnet`, `make test`, `make gate BASE=origin/dev`, `make emit-check`,
loader fixture tests, architecture tests, `git diff --check`, and a repository
scan proving no legacy C# case declarations remain. Read every exit code.

- [ ] **Step 3: Commit the C0 renewal**

Run: `git commit -m "chore(harness): renew golden TOML C0 ceremony"`

Do not push.

- [ ] **Step 4: Write caller artifacts last**

`result.json` contains top-level `conclusion` with the required fields and exact
verdict enum. `log.md` records baseline, RED/GREEN, equivalence, test, gate,
emit-check, commit, and no-push evidence. Create `done.sentinel` only after both
files are complete and parseable.
