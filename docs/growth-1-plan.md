# Growth-1 Capacity Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add fail-closed lane cleanup, content-addressed Lean report reuse, engineering-step deduplication, and machine-readable local gate timing without changing admission semantics.

**Architecture:** Worktree classification and destructive mutation live in the typed StrataLint CLI behind a thin Make/script adapter. Lean report equivalence is decided before production by one report-pair helper that hashes the invoked inspector, managed Lean sources, and pinned Lean configuration. Local and shared gates retain their authority boundaries while exchanging nested timing records through an absolute `STRATALINT_TIMING` file.

**Tech Stack:** .NET 10/C# 14, xUnit, Bash, Git worktrees/refs, Lean 4 inspector, GitHub Actions, Make.

---

### Task 1: Type And Test Clean-Lanes Classification

**Files:**

- Create: `Meta/StrataLint/StrataLint.Tests/Commands/CleanLanesCommandTests.cs`
- Create: `Meta/StrataLint/StrataLint.Cli/Commands/Worktrees/CleanLanesCommand.cs`
- Modify: `Meta/StrataLint/StrataLint.Cli/Commands/CliApplication.cs`
- Modify: `Meta/StrataLint/StrataLint.Cli/Admission/ProductionCliEnvironment.cs`
- Modify: `Meta/StrataLint/StrataLint.Tests/Admission/CliOutcomeTests.cs`

- [ ] **Step 1: Write failing integration tests for dry-run, force, and protected states**

Create real temporary Git repositories and linked worktrees. The public command
must be exercised rather than a mocked classifier:

```csharp
[Fact]
public void DryRunListsCleanMergedLaneWithoutMutation()
{
    using var fixture = CleanLanesFixture.Create();
    var lane = fixture.AddMergedLane("harness/merged");
    var result = fixture.Run();

    Assert.Equal(0, result.ExitCode);
    Assert.True(Directory.Exists(lane));
    Assert.Contains("\"kind\":\"merged_worktree\"", result.Output);
    Assert.Contains("\"action\":\"would_remove\"", result.Output);
}

[Fact]
public void ForceRemovesOnlyCleanMergedLaneAndItsObservedRef()
{
    using var fixture = CleanLanesFixture.Create();
    var removable = fixture.AddMergedLane("harness/merged");
    var dirty = fixture.AddMergedLane("harness/dirty", dirty: true);
    var unmerged = fixture.AddUnmergedLane("harness/unmerged");
    var result = fixture.Run("--force");

    Assert.Equal(0, result.ExitCode);
    Assert.False(Directory.Exists(removable));
    Assert.True(Directory.Exists(dirty));
    Assert.True(Directory.Exists(unmerged));
    Assert.False(fixture.LocalBranchExists("harness/merged"));
}
```

Add separate tests for an ancestor orphan branch, an unmerged orphan, the
current worktree, an attached `/tmp/trureturing-*` path, a same-repository
detached remnant, a foreign temp directory, and a ref moved after inventory.

- [ ] **Step 2: Run the tests and verify the expected red failure**

Run:

```bash
dotnet test Meta/StrataLint/StrataLint.Tests/StrataLint.Tests.csproj \
  --configuration Release --no-restore \
  --filter 'FullyQualifiedName~CleanLanesCommandTests' --verbosity minimal
```

Expected: compilation fails because `clean-lanes` routing and
`CleanLanesCommand` do not exist.

- [ ] **Step 3: Implement minimal parse, inventory, and stable JSONL output**

Add the CLI contract:

```csharp
internal sealed record CleanLanesOptions(string Base, bool Force);

internal static class CleanLanesCommand
{
    internal const string Usage =
        "USAGE: StrataLint clean-lanes [--base REV] [--force]";

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments) =>
        Run(repositoryRoot, arguments, new ProductionWorktreeProcessRunner(), ["/tmp"]);
}
```

Parse `git worktree list --porcelain -z`, resolve the base commit, require
managed branch grammar, read dirtiness with `status --porcelain=v1 -z`, and use
`merge-base --is-ancestor`. Sort records by kind, path, and branch before JSON
serialization.

- [ ] **Step 4: Add force mutations with exact observed identities**

For eligible worktrees, re-read status/head/branch, run `git worktree remove`,
then delete the local branch only through:

```csharp
RunRequired(
    runner,
    "git",
    ["update-ref", "-d", $"refs/heads/{branch}", observedHead],
    repositoryRoot,
    TimeSpan.FromSeconds(30),
    "managed branch moved during cleanup");
```

Validate detached temp remnants against the absolute common Git directory.
Reject symlinks, attached branches, foreign `.git` pointers, and ambiguous
metadata. Never remove the current root or a remote ref.

- [ ] **Step 5: Route and verify the command**

Add `CleanLanes` to `ICliEnvironment`, `ProductionCliEnvironment`, the test
stub, root usage, and command switch. Re-run the Task 1 filter. Expected: all
clean-lanes tests pass with no warning output.

### Task 2: Publish The Thin Make Adapter

**Files:**

- Create: `Meta/StrataLint/scripts/clean-lanes.sh`
- Modify: `Makefile`
- Modify: `Meta/StrataLint/StrataLint.Tests/Commands/MakeWorkflowTests.cs`

- [ ] **Step 1: Extend Make workflow tests first**

Add `clean-lanes` to the exact target array and assert its sole recipe delegates
to the adapter. Assert help documents dry-run and `FORCE=1`:

```csharp
Assert.Contains(CleanLanesScriptPath, Recipe(makefile, "clean-lanes"), StringComparison.Ordinal);
Assert.Contains("FORCE=1", helpOutput, StringComparison.Ordinal);
```

- [ ] **Step 2: Verify red, then add the adapter and target**

Run `MakeWorkflowTests`; expect failure because the target is absent. Add a
PATH-restoring adapter whose final command is:

```bash
exec dotnet run \
  --project "$ROOT/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj" \
  --configuration Release -- \
  clean-lanes --base "$BASE" "${FORCE_ARGS[@]}"
```

Keep one Make recipe. `make clean-lanes` is dry-run and
`make clean-lanes FORCE=1` passes `--force`.

- [ ] **Step 3: Re-run focused suites and commit**

Run clean-lanes and Make workflow filters, `bash -n` the adapter, then run the
real `make clean-lanes BASE=origin/dev` only in dry-run. Commit:

```bash
git add Makefile Meta/StrataLint/scripts/clean-lanes.sh \
  Meta/StrataLint/StrataLint.Cli Meta/StrataLint/StrataLint.Tests
git commit -m "feat(harness): add fail-closed lane cleanup"
```

### Task 3: Reuse Equivalent Lean Report Inputs

**Files:**

- Create: `Meta/StrataLint/scripts/lean-report-pair.sh`
- Create: `Meta/StrataLint/StrataLint.Tests/Commands/LeanReportPairScriptTests.cs`
- Modify: `Meta/StrataLint/scripts/local-harness-gate.sh`
- Modify: `.github/workflows/ci.yml`
- Modify: `Meta/StrataLint/StrataLint.Tests/Admission/ReviewRegressionTests.cs`

- [ ] **Step 1: Write fake-producer red tests**

Build two minimal roots containing `Trureturing.lean`, `D5/*.lean`,
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. A fake producer
increments a counter and writes report plus SHA sidecar:

```csharp
[Fact]
public void EqualInputsRunProducerOnceAndAttestBaselineReuse()
{
    using var fixture = LeanReportPairFixture.EqualInputs();
    var result = fixture.Run();

    Assert.Equal(0, result.ExitCode);
    Assert.Equal(1, fixture.ProducerInvocationCount);
    Assert.Equal(fixture.CandidateReportBytes, fixture.BaselineReportBytes);
    Assert.Equal("reused", fixture.BaselineProvenance.GetProperty("mode").GetString());
}
```

Add a theory covering source, toolchain, lake manifest, lakefile, and producer
mutations; every mutation must invoke the producer twice.

- [ ] **Step 2: Run and observe the missing-script failure**

Run the `LeanReportPairScriptTests` filter. Expected: red because the helper is
absent.

- [ ] **Step 3: Implement canonical input addresses and provenance**

Hash this versioned preimage:

```text
schema=stratalint-lean-report-input-v1
inspector_sha256=<inspect.sh + Inspector.lean manifest hash>
sources_sha256=<Trureturing.lean + sorted D5/**/*.lean manifest hash>
lean_toolchain_sha256=<hash>
lakefile_toml_sha256=<hash>
lake_manifest_sha256=<hash>
```

Equal addresses run candidate production once and copy exact bytes; unequal
addresses run the same producer independently for both roots. Verify nonempty
reports and sidecars. Write `<report>.provenance.json` containing schema, side,
mode, source side, input address, and report SHA-256.

- [ ] **Step 4: Replace both duplicated call sites**

Local gate invokes the candidate helper with the base-owned producer. CI invokes
the base helper, with candidate-helper bootstrap only when the exact baseline
predates its introduction; disappearance after introduction fails closed. Keep
report names and upload paths unchanged.

- [ ] **Step 5: Run red/green and trust-topology tests**

Run `bash -n`, the report-pair filter, and
`Cf10WorkflowSeparatesLeanInspectionFromDotnetAdmission`. Expected: equal count
1, mismatch count 2, and .NET admission still never invokes Lean.

### Task 4: Deduplicate Engineering And Emit Gate Timings

**Files:**

- Modify: `Meta/StrataLint/scripts/preflight.sh`
- Modify: `Meta/StrataLint/scripts/local-harness-gate.sh`
- Modify: `.github/scripts/harness-gate.sh`
- Modify: `Makefile`
- Modify: `Meta/StrataLint/StrataLint.Tests/Commands/MakeWorkflowTests.cs`

- [ ] **Step 1: Add contract tests before behavior**

```csharp
Assert.Contains("--skip-engineering", preflight, StringComparison.Ordinal);
Assert.Contains("--skip-engineering", localGate, StringComparison.Ordinal);
Assert.Contains("STRATALINT_TIMING", sharedGate, StringComparison.Ordinal);
Assert.Contains("gate_stage_timing", localGate, StringComparison.Ordinal);
Assert.Contains("gate_timing_summary", localGate, StringComparison.Ordinal);
Assert.DoesNotContain("STRATALINT_TIMING:-1", sharedGate, StringComparison.Ordinal);
```

Run `MakeWorkflowTests`; expected red.

- [ ] **Step 2: Add explicit engineering skip with unchanged defaults**

Parse `--skip-engineering` in local gate. False runs existing
dotnet/test/selftest exactly as before; true emits skipped timing records.
Preflight explicitly calls:

```bash
make gate BASE="${BASE:-origin/dev}" GATE_ARGS=--skip-engineering
```

and the Make recipe appends `$(GATE_ARGS)` to the canonical script invocation.

- [ ] **Step 3: Connect shared and local timing**

Each local or nested admission stage emits JSON Lines:

```json
{"event":"gate_stage_timing","scope":"local","stage":"lean-reports","status":"passed","elapsed_seconds":192}
```

Set `STRATALINT_TIMING` to an absolute temporary JSONL file for the shared gate.
Its existing `mark` appends `scope:"admission"`; reject non-absolute paths and
remove the unused boolean default. The local EXIT trap preserves rc, cleans the
judge/temp tree, prints all stages, and ends with one `gate_timing_summary` JSON
record even on failure.

- [ ] **Step 4: Run syntax/focused tests and commit**

Run `bash -n` for all changed scripts and the Make/workflow filters. Commit:

```bash
git add Makefile .github Meta/StrataLint
git commit -m "perf(harness): reuse Lean reports and expose gate timings"
```

### Task 5: Renew The Existing C0 Ceremony Without Changing It

**Files:**

- Modify: `Meta/StrataLint/TOWER.yaml`
- Modify: `Meta/StrataLint/Golden/c0-inaugural-conservative-certificate.json`
- Append: `Meta/StrataLint/Architecture/HARDCODE-LEDGER.md`
- Modify: `docs/develop/spec/golden-ledger-repo-spec.md`

- [ ] **Step 1: Freeze the implementation preimage**

Require a clean tracked tree and record exact `HEAD` and `HEAD^{tree}`. Produce
fresh candidate/baseline reports through the new pair helper.

- [ ] **Step 2: Run the unchanged base-owned conservative verifier**

Build both harnesses and invoke exact `origin/dev` verifier inputs. Capture the
one-line certificate. Require verifier rc 0, `CORPUS_CONSERVATIVE`, empty
findings, and equal baseline/preserved admit counts. Do not edit verifier,
corpus, rule set, or exit mapping to obtain it.

- [ ] **Step 3: Rebind the canonical ceremony records**

Replace certificate bytes with verified output. Update only existing C0 TOWER
addresses: recursive controller/corpus blobs, gate wiring blob, certificate
SHA-256, exact base commit, and preimage commit/tree. Append run inputs, reuse,
counts, and autopsies to HARDCODE-LEDGER. Add the operational class to the sole
canonical repository spec without creating a second normative source.

- [ ] **Step 4: Verify and commit renewal**

Run all `C0CeremonyTrustRootTests`, full architecture tests, and
`git diff --check`. Commit certificate/TOWER/spec/ledger renewal separately:

```bash
git commit -m "chore(harness): renew growth-1 C0 ceremony"
```

### Task 6: Full Acceptance, Independent Review, And Delivery

**Files:**

- Create at completion: `.sshx-result.json`
- Create last: `.sshx-done`

- [ ] **Step 1: Run focused behavior verification**

Run clean-lanes, report-pair, Make workflow, trust-topology, shell syntax, real
dry-run, and one force run entirely inside a disposable fixture.

- [ ] **Step 2: Run the full local CI predictor**

```bash
make preflight BASE=origin/dev
```

Expected: engineering executes once, local gate records those stages as skipped,
equivalent Lean inputs invoke inspector once with reuse attestation, admission
semantics stay green, and output ends its local-gate section with timing JSON.

- [ ] **Step 3: Run independent review and repair findings**

Review committed diff against `origin/dev` for unsafe deletion, equivalence
false positives, provenance gaps, shell EXIT behavior, trust changes, and tests.
Apply fixes through new red tests and rerun affected gates.

- [ ] **Step 4: Push and verify remote identity**

Require empty `git status --porcelain`, push, then verify:

```bash
test "$(git rev-parse HEAD)" = "$(git rev-parse origin/harness/growth-1)"
```

- [ ] **Step 5: Write completion envelope and sentinel**

Write `.sshx-result.json` with final commit/base, verification commands and exit
codes, report addresses/reuse, timing summary, review result, and the explicit
missing growth-audit attachment constraint. Validate JSON. Create `.sshx-done`
only after required fields and remote identity checks succeed.
