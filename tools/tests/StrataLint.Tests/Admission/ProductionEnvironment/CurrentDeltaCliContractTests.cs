using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.EngineeringScope;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Tests;

[CollectionDefinition("CI fixture environment", DisableParallelization = true)]
public sealed class CiFixtureEnvironmentCollection;

[Collection("CI fixture environment")]
public sealed partial class CurrentDeltaCliContractTests(Xunit.Abstractions.ITestOutputHelper log)
{
    public static int Main(string[] arguments)
    {
        var root = Environment.CurrentDirectory;
        return CliApplication.Run(arguments,
            new ProductionCliEnvironment(root, new GitRepositoryGateway(root), new PrecomputedLeanReportSource(root)),
            new SystemCliConsole());
    }

    [Theory]
    [InlineData("valid", 0, "ADMITTED")]
    [InlineData("invalid-report", 2, "Raw Lean report is not valid JSON")]
    [InlineData("retired-option", 2, "harness-gate: unknown argument '--test-map-cache-root'")]
    public void HarnessGateUsesActualCandidateCheckCli(string scenario, int expectedExit, string diagnostic)
    {
        if (OperatingSystem.IsWindows()) throw new PlatformNotSupportedException();
        using var temporary = new TemporaryDirectory();
        var root = Encoding.UTF8.GetString(RequireSuccess(TestProcessRunner.Run("pwd", ["-P"],
            temporary.Path, TestBudgets.ScriptProcessHangGuard, 4096)).StandardOutput).Trim();
        var repository = TestRepositoryLayout.FindRoot();
        var bin = Path.Combine(root, "bin");
        Directory.CreateDirectory(bin);
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        foreach (var (path, content) in fixture.Files)
        {
            var destination = Path.Combine(root, path);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.WriteAllText(destination, content);
        }
        File.WriteAllText(Path.Combine(root, ".gitignore"), "bin/\n.lake/\ntools/StrataLint.Cli/bin/\n");
        Git("init", "-q");
        Git("add", ".");
        Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "base");
        var basis = Encoding.UTF8.GetString(Git("rev-parse", "HEAD").StandardOutput).Trim();
        var report = Path.Combine(root, ".lake/report.json");
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(GitRepositorySnapshotReader.ReadCurrent(root))).Snapshot;
        RawLeanReportArtifact.WriteFile(report, snapshot, LeanAxiomReport.Create(fixture.Reports));
        if (scenario == "invalid-report") File.WriteAllText(report, "not JSON\n");

        var runtime = Path.Combine(root, "tools/StrataLint.Cli/bin/Release/net10.0");
        Directory.CreateDirectory(Path.GetDirectoryName(runtime)!);
        Directory.CreateSymbolicLink(runtime, Path.GetDirectoryName(typeof(StrataLint.Cli.Program).Assembly.Location)!);
        // Reuse the candidate build. The native host calls the actual check consumer;
        // the separate filemap stage retains its process-normalization test boundary.
        WriteExecutable(Path.Combine(bin, "make"), """
            [[ $# == 3 && "$1" == -C && "$2" == "$GATE_TEST_ROOT/tools" && "$3" == dotnet ]]
            test -s "$GATE_TEST_ROOT/tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"
            """);
        WriteExecutable(Path.Combine(bin, "dotnet"), """
            [[ "$1" == "$GATE_TEST_ROOT/tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll" ]]
            if [[ $# == 2 && "$2" == filemap-conform ]]; then exit 0; fi
            shift
            exec "$GATE_TEST_DOTNET" "$GATE_TEST_HOST" "$@"
            """);
        var dotnet = Encoding.UTF8.GetString(RequireSuccess(TestProcessRunner.Run("/bin/bash",
            ["-c", "command -v dotnet"], root, TestBudgets.ScriptProcessHangGuard, 4096)).StandardOutput).Trim();
        var arguments = new List<string>
        {
            $"PATH={bin}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
            $"GATE_TEST_ROOT={root}", $"GATE_TEST_DOTNET={dotnet}",
            $"GATE_TEST_HOST={typeof(CurrentDeltaCliContractTests).Assembly.Location}",
            Path.Combine(repository, ".github/scripts/harness-gate.sh"),
            "--candidate", root, "--base", basis, "--candidate-lean-report", report,
        };
        if (scenario == "retired-option") arguments.AddRange(["--test-map-cache-root", Path.Combine(root, "test-maps")]);
        var result = TestProcessRunner.Run("/usr/bin/env", arguments, root,
            TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        var output = Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError);
        log.WriteLine(JsonSerializer.Serialize(new { executable = "/usr/bin/env", arguments, result.ExitCode, output }));
        Assert.True(result.ExitCode == expectedExit, $"expected {expectedExit}, got {result.ExitCode}: {output}");
        Assert.True(output.Contains(diagnostic, StringComparison.Ordinal), $"missing {diagnostic}: {output}");
        Assert.False(Directory.Exists(Path.Combine(root, "test-maps")));

        ProcessOutput Git(params string[] args) => RequireSuccess(TestProcessRunner.Run("git", args,
            root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024));
    }

    [Fact]
    public void ActualCandidateCheckCliRejectsRetiredTestMapOption()
    {
        using var temporary = new TemporaryDirectory();
        var result = TestProcessRunner.Run("dotnet", [typeof(StrataLint.Cli.Program).Assembly.Location, "check",
            "--protected-base", new string('a', 40), "--candidate-lean-report", "missing.json",
            "--test-map-cache-root", "test-maps"], temporary.Path,
            TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        log.WriteLine(JsonSerializer.Serialize(new { assembly = typeof(StrataLint.Cli.Program).Assembly.Location, result.ExitCode, error = Encoding.UTF8.GetString(result.StandardError) }));
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("USAGE: StrataLint check", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
    }

    private static ProcessOutput RequireSuccess(ProcessOutput result)
    {
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        return result;
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteExecutable(string path, string body)
    {
        File.WriteAllText(path, "#!/usr/bin/env bash\nset -euo pipefail\n" + body + "\n");
        File.SetUnixFileMode(path, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }

    [Theory]
    [InlineData("all")]
    [InlineData("selected")]
    [InlineData("metadata")]
    [InlineData("metadata-seed-miss")]
    [InlineData("metadata-required-report")]
    [InlineData("metadata-forged-candidate")]
    [InlineData("metadata-missing-registration")]
    public void CurrentHonorsRegisteredChecksInParentlessRemotelessRepository(string scenario)
    {
        var selected = scenario != "all";
        var metadata = scenario.StartsWith("metadata", StringComparison.Ordinal);
        string[] selectedChecks = metadata && scenario != "metadata-required-report"
            ? ["SL-003", "SL-015", "SL-019"] : ["SL-012"];
        using var ciEnvironment = new CiFixtureEnvironment();
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Meta/ci-checks.json"] = CommonCheckRegistrationFixture.Manifest("tools/StrataLint.Scribe/StrataLint.Scribe.csproj");
        fixture.Files["global.json"] = "{\"sdk\":{\"version\":\"10.0.103\"}}";
        fixture.Files["tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs"] = "// banned-api-proof\n";
        if (selected)
        {
            const string producer = "Meta/ReportProducers/lean-report.json";
            const string consumer = "Meta/ReportConsumers/lean-report.json";
            fixture.Files[producer] = "{\"schema\":\"report-producer-scope-v2\",\"registration\":\"lean-report-inputs.json\",\"scope\":\"lean-report\",\"projects\":[]}";
            fixture.Files["lean-report-inputs.json"] = "{\"producer_scopes\":{\"lean-report\":{\"include\":[{\"pattern\":\"global.json\",\"optional\":false}],\"exclude\":[]}}}";
            fixture.Files[consumer] = JsonSerializer.Serialize(new
            {
                schema = "report-consumer-inputs-v1", producer, projects = Array.Empty<string>(), materials = new[] { "global.json" },
            });
            var registration = JsonNode.Parse(fixture.Files[CommonExecutionEvidence.CheckManifestPath])!;
            registration["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == "SL-012")!["report_inputs"] =
                JsonSerializer.SerializeToNode(new[] { new { producer, consumer, artifact = "raw-lean-report", materials = new[] { "global.json" } } });
            fixture.Files[CommonExecutionEvidence.CheckManifestPath] = registration.ToJsonString();
            var repository = TestRepositoryLayout.FindRoot();
            foreach (var path in new[] { "tools/scripts/workflow/ci.py", "tools/scripts/workflow/ci_plan.py" })
                fixture.Files[path] = File.ReadAllText(Path.Combine(repository, path));
            fixture.Files["Meta/ci-resources.json"] = JsonSerializer.Serialize(new {
                schema = "ci-resource-execution-v1", resources = new[] {
                    new { id = "current", projects = new[] { "tools/StrataLint.Scribe/StrataLint.Scribe.csproj" },
                        checks = selectedChecks, steps = metadata ? ["check-current"] : new[] { "check-current", "lean-report" } } } });
            var policy = FileMapLoader.Parse(Encoding.UTF8.GetBytes(TestFileMap.Canonical), "current fixture");
            var entries = policy.Entries.Select(entry => new FileMapEntry(
                entry.Pattern,
                entry.Kind,
                entry.AdmissionPlane,
                entry.ProducedBy,
                entry.ConsumedBy,
                entry.VerifiedBy,
                entry.ResidenceViolation,
                entry.ArtifactId,
                entry.Mode,
                entry.RuntimeDisposition,
                entry.HistoryRequirement,
                ["current"],
                entry.Symlink,
                entry.DigestionSource)).ToImmutableArray();
            var current = new FileMapResource(
                "current",
                "current",
                "tools/scripts/workflow/ci.py",
                [],
                [],
                [],
                ImmutableDictionary<string, string>.Empty,
                ["Meta/ci-checks.json", "Meta/ci-resources.json", "Meta/engineering-projects.json"]);
            fixture.Files["Meta/FILEMAP.toml"] = Encoding.UTF8.GetString(FileMapCanonicalWriter.Write(
                new FileMapManifest(policy.ResidencePolicy, entries, policy.ArtifactKinds, [current])).AsSpan());
        }
        foreach (var pair in fixture.Files)
        {
            var file = Path.Combine(temporary.Path, pair.Key);
            Directory.CreateDirectory(Path.GetDirectoryName(file)!);
            File.WriteAllText(file, pair.Value);
        }
        File.WriteAllText(Path.Combine(temporary.Path, ".gitignore"), ".lake/\nbuild/\n__pycache__/\n");
        Git(temporary.Path, "init", "-q");
        Git(temporary.Path, "add", ".");
        Git(temporary.Path, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "parentless");
        var report = Path.Combine(temporary.Path, ".lake/build/stratalint/raw-lean-report.json");
        if (!metadata) WriteReport();
        var environment = new ProductionCliEnvironment(temporary.Path, new GitRepositoryGateway(temporary.Path), new FakeLeanReportSource(null));
        var arguments = Arguments();
        if (scenario == "metadata-seed-miss")
        {
            var root = temporary.Path;
            var seedBuild = CommonExecutionEvidence.Read<CommonStageRecord>(root, CommonExecutionEvidence.BuildPath);
            var seedChecks = CommonExecutionEvidence.BeginChecks(root, "current", seedBuild, TextWriter.Null, selectedChecks);
            foreach (var id in selectedChecks)
                seedChecks.Run(id, () => new([new(id, 0, CommonCheckRegistrationFixture.Predicate(id))]));
            _ = seedChecks.Seal();
            _ = CommonExecutionEvidence.CompleteCurrent(root, seedBuild, [], ResourceExecutionPlan.Load(root, "build/plan.json", "build/scope.json"));
            Assert.True(CommonExecutionEvidence.ExportCheckSeed(root, "current", TextWriter.Null));
            var seed = Path.Combine(root, CommonExecutionEvidence.CheckSeedPath("current"));
            var record = CommonExecutionEvidence.Read<CommonCheckRecord>(seed, "checks.json");
            CommonExecutionEvidence.Write(seed, "checks.json", record with
            {
                Units = record.Units.Select(unit => unit with { InputFingerprint = new string('0', 64) }).ToArray(),
            });
        }
        if (scenario == "metadata-required-report")
        {
            Assert.Empty(arguments);
            Assert.False(Directory.Exists(Path.Combine(temporary.Path, ".lake")));
            Assert.False(File.Exists(Path.Combine(temporary.Path, CommonExecutionEvidence.ChecksPath("current"))));
            return;
        }
        if (scenario == "metadata-forged-candidate")
        {
            var build = CommonExecutionEvidence.Read<CommonStageRecord>(temporary.Path, CommonExecutionEvidence.BuildPath);
            CommonExecutionEvidence.Write(temporary.Path, CommonExecutionEvidence.BuildPath, build with { Candidate = new string('0', 64) });
        }
        if (scenario == "metadata-missing-registration")
            File.Delete(Path.Combine(temporary.Path, CommonExecutionEvidence.CheckManifestPath));
        var reads = 0;
        var manifestReads = 0;
        var previous = RawLeanReportArtifact.Reading.Value;
        var previousManifest = CommonExecutionEvidence.ReadingCheckManifest.Value;
        var previousPath = Environment.GetEnvironmentVariable("PATH");
        using var executables = new TemporaryDirectory();
        if (metadata)
        {
            foreach (var name in new[] { "git", "python3" })
            {
                var executable = Encoding.UTF8.GetString(RequireSuccess(TestProcessRunner.Run("/bin/sh",
                    ["-c", "command -v " + name], temporary.Path, TestBudgets.ScriptProcessHangGuard, 4096)).StandardOutput).Trim();
                File.CreateSymbolicLink(Path.Combine(executables.Path, name), executable);
            }
            Environment.SetEnvironmentVariable("PATH", executables.Path);
            Assert.False(File.Exists(Path.Combine(executables.Path, "lake")));
        }
        ExplicitCommandResult result;
        try
        {
            RawLeanReportArtifact.Reading.Value = () => reads++;
            CommonExecutionEvidence.ReadingCheckManifest.Value = () => manifestReads++;
            result = environment.CheckCurrent(arguments);
        }
        finally
        {
            RawLeanReportArtifact.Reading.Value = previous;
            CommonExecutionEvidence.ReadingCheckManifest.Value = previousManifest;
            Environment.SetEnvironmentVariable("PATH", previousPath);
        }
        if (metadata)
        {
            log.WriteLine("REPORTLESS_CURRENT scenario={0} exit={1} report_reads={2}: {3}{4}",
                scenario, result.ExitCode, reads, result.Output, result.Error);
            Assert.Equal(0, reads);
            Assert.False(Directory.Exists(Path.Combine(temporary.Path, ".lake")));
            if (scenario is not ("metadata" or "metadata-seed-miss"))
            {
                Assert.Equal(2, result.ExitCode);
                Assert.Contains(scenario switch
                {
                    "metadata-forged-candidate" => "candidate identity",
                    _ => CommonExecutionEvidence.CheckManifestPath,
                }, result.Error, StringComparison.Ordinal);
                Assert.False(File.Exists(Path.Combine(temporary.Path, CommonExecutionEvidence.ChecksPath("current"))));
                Assert.False(File.Exists(Path.Combine(temporary.Path, CommonExecutionEvidence.CurrentPath)));
                return;
            }
            Assert.True(result.ExitCode == 0, result.Output + result.Error);
            if (scenario == "metadata-seed-miss")
            {
                foreach (var id in selectedChecks)
                    Assert.Contains($"COMMON_CHECK_SEED_MISS id={id} reason=\"invalid common check identity/provenance: {id}\"", result.Output, StringComparison.Ordinal);
                Assert.DoesNotContain("COMMON_CHECK_SEED_UNAVAILABLE", result.Output, StringComparison.Ordinal);
                Assert.DoesNotContain("COMMON_CHECK_REUSED", result.Output, StringComparison.Ordinal);
            }
            Assert.Equal(1, manifestReads);
            var checks = CommonExecutionEvidence.Read<CommonCheckRecord>(temporary.Path, CommonExecutionEvidence.ChecksPath("current"));
            Assert.Equal(selectedChecks, checks.Units.Select(unit => unit.Id));
            Assert.All(checks.Units, unit =>
            {
                Assert.Equal("executed", unit.Status);
                Assert.Equal("passed", unit.Result);
                Assert.Null(unit.Report);
                Assert.DoesNotContain(unit.Materials, material => material.Path.StartsWith(".lake/", StringComparison.Ordinal));
            });
            var build = CommonExecutionEvidence.ValidateBuild(temporary.Path);
            var plan = ResourceExecutionPlan.Load(temporary.Path, "build/plan.json", "build/scope.json");
            _ = CommonExecutionEvidence.CompleteCurrent(temporary.Path, build, [], plan);
            var verified = CommonExecutionEvidence.ValidateCurrent(temporary.Path);
            Assert.Equal(build.Candidate, verified.Candidate);
            Assert.Equal(build.Round, verified.Round);
            Assert.Equal(selectedChecks, CommonExecutionEvidence.CurrentCheckIds(temporary.Path));
            Assert.DoesNotContain(verified.Materials, material => material.Path.StartsWith(".lake/", StringComparison.Ordinal));
            return;
        }
        Assert.True(result.ExitCode == 0, result.Output + result.Error);
        if (selected)
        {
            // One initial read, one after the selected predicate writes its retained
            // material, and one at seal. The initial CLI and input owner share a read.
            Assert.Equal(3, reads);
            Assert.Equal(new[] { "SL-012" }, CommonExecutionEvidence.Read<CommonCheckRecord>(temporary.Path,
                CommonExecutionEvidence.ChecksPath("current")).Units.Select(unit => unit.Id));
            using var verdict = JsonDocument.Parse(result.Output[result.Output.IndexOf("{\"executed\"", StringComparison.Ordinal)..]);
            Assert.Equal(new[] { "SL-012" }, verdict.RootElement.GetProperty("executed").EnumerateArray().Select(value => value.GetString()));
            File.AppendAllText(report, "damage");
            var damaged = environment.CheckCurrent(arguments);
            Assert.Equal(2, damaged.ExitCode);
            Assert.Contains("Raw Lean report", damaged.Error, StringComparison.Ordinal);
        }
        File.WriteAllText(Path.Combine(temporary.Path, RuleFixture.RingPath), "def invalid : Nat := 0\n");
        WriteReport();
        result = environment.CheckCurrent(Arguments());
        Assert.Equal(1, result.ExitCode);
        Assert.Contains("SL-012", result.Output, StringComparison.Ordinal);

        string[] Arguments()
        {
            if (!selected) return ["--candidate-lean-report", report];
            var root = temporary.Path;
            const string log = "build/ci/fixture-build.log";
            Directory.CreateDirectory(Path.Combine(root, "build/ci"));
            File.WriteAllText(Path.Combine(root, log), "fixture build material");
            var build = CommonExecutionEvidence.SealBuild(root, CommonExecutionEvidence.Candidate(root), [log],
                CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", log)).ToArray());
            var commit = Git(root, "rev-parse", "HEAD");
            var entry = Git(root, "ls-tree", "HEAD", "--", RuleFixture.RingPath).Split([' ', '\t'], StringSplitOptions.RemoveEmptyEntries);
            var changes = Path.Combine(root, "build/scope.json");
            var plan = Path.Combine(root, "build/plan.json");
            File.WriteAllText(changes, JsonSerializer.Serialize(new { schema_version = 1, mode = "current",
                candidate = new { commit, tree = Git(root, "rev-parse", "HEAD^{tree}") }, @base = (string?)null, head = (string?)null,
                complete = true, change_count = 1, changes = new[] { new { status = "A", old = (object?)null,
                    @new = new { path = RuleFixture.RingPath, mode = entry[0], oid = entry[2] } } } }));
            var planning = TestProcessRunner.Run("python3", ["-B", "tools/scripts/workflow/ci.py", "plan", "--repository", root,
                "--commit", commit, "--changes", changes, "--output", plan], root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
            if (scenario == "metadata-required-report")
            {
                Assert.NotEqual(0, planning.ExitCode);
                Assert.Contains("selected check requires lean-report: SL-012", Encoding.UTF8.GetString(planning.StandardError), StringComparison.Ordinal);
                Assert.False(File.Exists(plan));
                return [];
            }
            Assert.True(planning.ExitCode == 0, Encoding.UTF8.GetString(planning.StandardError));
            return [.. metadata ? Array.Empty<string>() : new[] { "--candidate-lean-report", report },
                "--common-build-round", build.Round, "--common-plan", plan, "--common-changes", changes];
        }

        void WriteReport()
        {
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(GitRepositorySnapshotReader.ReadCurrent(temporary.Path))).Snapshot;
            RawLeanReportArtifact.WriteFile(report, snapshot, LeanAxiomReport.Create(fixture.Reports));
            foreach (var suffix in new[] { ".sha256", ".input.attestation", ".provenance.json" })
                File.WriteAllText(report + suffix, "fixture companion\n");
        }
    }

    [Fact]
    public void CurrentRejectsABaseOptionBeforeRepositoryPreparation()
    {
        var environment = new ProductionCliEnvironment("/missing-repository");
        var result = environment.CheckCurrent(["--protected-base", new string('a', 40), "--candidate-lean-report", "missing"]);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("accepts no base", result.Error, StringComparison.Ordinal);
    }

    private static string Git(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run("git", arguments, root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        return Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    [Theory]
    [InlineData("valid", 0, "")]
    [InlineData("reused", 0, "")]
    [InlineData("template-changed-undeclared", 1, "DTR-Undeclared")]
    [InlineData("template-unchanged", 3, "SL-022")]
    [InlineData("template-missing-evidence", 1, "DTR-Evidence")]
    [InlineData("disabled-base-project", 2, "base test project")]
    [InlineData("premanifest-base", 0, "")]
    [InlineData("premanifest-missing-base-project", 2, "base test project")]
    [InlineData("original-registration-base", 0, "")]
    [InlineData("original-registration-missing-base-project", 2, "base test project")]
    [InlineData("annotation", 3, "SL-022")]
    [InlineData("mixed", 1, "SL-029")]
    [InlineData("retired-content-delete", 1, "SL-029")]
    [InlineData("retired-content-rename", 1, "SL-029")]
    [InlineData("first-freeze", 1, "SL-008")]
    [InlineData("ratchet", 1, "SL-003")]
    [InlineData("unowned-project", 1, "TEST_PROJECT_TOPOLOGY candidate introduces topology debt: missing-owned-project StrataLint.NewProduct -> StrataLint.NewProduct.Tests")]
    [InlineData("missing-base-project", 2, "base test project")]
    [InlineData("missing-report", 2, "")]
    [InlineData("candidate-mismatch", 2, "candidate identity")]
    [InlineData("failed-trx", 2, "artifact integrity")]
    [InlineData("missing-current", 2, "current.json")]
    [InlineData("after-valid-missing-report", 2, "raw-lean-report.json")]
    [InlineData("after-valid-invalid-report", 2, "Raw Lean report is not valid JSON")]
    [InlineData("after-valid-missing-report-archive", 2, "materials")]
    [InlineData("after-valid-stale-report", 2, "source")]
    [InlineData("after-valid-candidate-mismatch", 2, "candidate identity")]
    [InlineData("after-valid-failed-trx", 2, "artifact integrity")]
    [InlineData("after-valid-current-round", 2, "round mismatch")]
    [InlineData("after-valid-unbound-report-archive", 2, "missing required materials")]
    [InlineData("after-valid-contradictory-material", 2, "artifact integrity")]
    [InlineData("staged-valid", 0, "")]
    [InlineData("staged-missing-current", 2, "current.json")]
    [InlineData("staged-failed-trx", 2, "artifact integrity")]
    [InlineData("staged-invalid-dll", 2, "artifact integrity")]
    [InlineData("staged-unbound-dll", 2, "unbound candidate binary")]
    [InlineData("staged-candidate-mismatch", 2, "candidate identity")]
    public void DeltaConsumesValidatedCommonResultsAndEnforcesOnlyCrossTreePredicates(string scenario, int expectedExit, string diagnostic)
    {
        var staged = scenario.StartsWith("staged-", StringComparison.Ordinal);
        var afterValid = scenario.StartsWith("after-valid-", StringComparison.Ordinal);
        var defect = staged ? scenario["staged-".Length..] : afterValid ? scenario["after-valid-".Length..] : scenario;
        var template = scenario.StartsWith("template-", StringComparison.Ordinal);
        using var temporary = new TemporaryDirectory();
        var root = temporary.Path;
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Meta/ci-checks.json"] = CommonCheckRegistrationFixture.Manifest("tools/StrataLint.Scribe/StrataLint.Scribe.csproj");
        fixture.Files["global.json"] = "{\"sdk\":{\"version\":\"10.0.103\"}}";
        fixture.Files["tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs"] = "// banned-api-proof\n";
        if (template)
        {
            foreach (var pair in DeclaredTemplateReviewTests.PolicyFiles()) fixture.Files[pair.Key] = pair.Value;
        }
        foreach (var pair in fixture.Files) Write(pair.Key, pair.Value);
        Write(".gitignore", ".lake/\nbuild/\ntools/StrataLint.Cli/bin/\n");
        var repository = TestRepositoryLayout.FindRoot();
        var filemapDocuments = FileMapDocuments.Resolve(
            File.ReadAllBytes(Path.Combine(repository, AdmissionPlanePolicy.FileMapPath)),
            AdmissionPlanePolicy.FileMapPath,
            path => File.ReadAllBytes(Path.Combine(repository, path)));
        foreach (var document in filemapDocuments)
            Write(document.Path, Encoding.UTF8.GetString(document.Bytes.AsSpan()));
        const string firstProject = "tools/tests/StrataLint.First/First.csproj";
        Write(firstProject, "<Project><PropertyGroup><IsTestProject>true</IsTestProject></PropertyGroup></Project>\n");
        Write("tools/tests/StrataLint.Second/Second.csproj", "<Project><PropertyGroup><IsTestProject>true</IsTestProject></PropertyGroup></Project>\n");
        var registration = JsonNode.Parse(fixture.Files[EngineeringRegistrationFixture.Path])!;
        var projects = registration["projects"]!.AsArray();
        foreach (var (path, assembly) in new[] { (firstProject, "First"), ("tools/tests/StrataLint.Second/Second.csproj", "Second") })
            projects.Add(JsonNode.Parse(EngineeringRegistrationFixture.Manifest(
                new EngineeringProjectFixture(path, assembly, "cross-cutting-test", true, [])))!["projects"]![0]!.DeepClone());
        Write(EngineeringRegistrationFixture.Path, registration.ToJsonString());
        if (scenario.StartsWith("premanifest-", StringComparison.Ordinal))
            File.Delete(Path.Combine(root, EngineeringRegistrationFixture.Path));
        if (scenario.StartsWith("original-registration-", StringComparison.Ordinal))
        {
            var historical = registration.DeepClone();
            historical.AsObject().Remove("rule_build_inputs");
            foreach (var row in historical["projects"]!.AsArray())
                foreach (var field in new[] { "root_namespace", "namespace_exclude", "global_namespace_exceptions" })
                    row!.AsObject().Remove(field);
            Write(EngineeringRegistrationFixture.Path, historical.ToJsonString());
        }
        const string retiredContent = "Retired/Content.md";
        if (scenario.StartsWith("retired-content-", StringComparison.Ordinal))
        {
            Write(retiredContent, "prior content\n");
            var filemap = TomlSerializer.Deserialize<TomlTable>(File.ReadAllText(Path.Combine(root, "Meta/FILEMAP.toml")))!;
            var entry = TomlSerializer.Deserialize<TomlTable>("""
                pattern = "Retired/Content.md"
                require = []
                kind = "data"
                admission_plane = "content"
                produced_by = "none"
                consumed_by = ["test"]
                verified_by = ["SnapshotDecoder"]
                artifact_id = "none"
                runtime_disposition = "committed-source"
                """)!;
            var rows = new TomlArray();
            foreach (var row in ((TomlArray)filemap["files"]).Cast<TomlTable>().Append(entry)
                .OrderBy(row => (string)row["pattern"], StringComparer.Ordinal)) rows.Add(row);
            filemap["files"] = rows;
            Write("Meta/FILEMAP.toml", TomlSerializer.Serialize(filemap));
        }
        const string protectedPath = "tools/scripts/probe.sh";
        Git(root, "init", "-q"); Git(root, "add", ".");
        Git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "base");
        var baseResult = TestProcessRunner.Run("git", ["rev-parse", "HEAD"], root, TestBudgets.ScriptProcessHangGuard, 1024);
        var basis = Encoding.UTF8.GetString(baseResult.StandardOutput).Trim();
        Write(EngineeringRegistrationFixture.Path, registration.ToJsonString());
        switch (scenario)
        {
            case "template-changed-undeclared":
            case "template-missing-evidence":
                Write(RuleFixture.RingPath, fixture.Files[RuleFixture.RingPath] + "-- changed candidate module\n");
                break;
            case "template-unchanged":
                Write(AdmissionPlanePolicy.FileMapPath, File.ReadAllText(Path.Combine(root, AdmissionPlanePolicy.FileMapPath))
                    + "\n# Judge metadata leaves historical template content unselected.\n");
                break;
            case "retired-content-delete":
            case "retired-content-rename":
                File.Delete(Path.Combine(root, retiredContent));
                Write("Meta/FILEMAP.toml", File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "Meta/FILEMAP.toml")));
                if (scenario == "retired-content-rename") Write("README.md", "prior content\n");
                break;
            case "premanifest-base": break;
            case "original-registration-base": break;
            case "annotation": Write(protectedPath, "#!/bin/sh\nexit 0\n"); break;
            case "mixed": Write("tools/StrataLint.Cli/probe.cs", "// candidate judge\n"); Write(RuleFixture.BlueprintPath, "# changed\n"); break;
            case "first-freeze": Write("Golden/Frozen/accepted/" + new string('a', 64) + ".json", "{}\n"); break;
            case "ratchet": for (var i = 0; i <= RepositoryRules.DirectoryFileLimit; i++) Write($"docs/reports/ratchet/{i}.json", "{}\n"); break;
            case "unowned-project":
                const string product = "tools/StrataLint.NewProduct/StrataLint.NewProduct.csproj";
                Write(product, "<Project />\n");
                projects.Add(JsonNode.Parse(EngineeringRegistrationFixture.Manifest(new EngineeringProjectFixture(
                    product, "StrataLint.NewProduct", "production", false, [], OwnedTestAssembly: "StrataLint.NewProduct.Tests")))!["projects"]![0]!.DeepClone());
                break;
            case "disabled-base-project":
                projects.Single(item => item!["path"]!.GetValue<string>() == firstProject)!["ci"] = false;
                break;
            case "missing-base-project":
            case "premanifest-missing-base-project":
            case "original-registration-missing-base-project":
                File.Delete(Path.Combine(root, firstProject));
                var removed = projects.Single(item => item!["path"]!.GetValue<string>() == firstProject)!;
                projects.Remove(removed);
                registration["historical_projects"]!.AsArray().Add(removed);
                break;
            default: Write(RuleFixture.BlueprintPath, "# changed\n"); break;
        }
        Write(EngineeringRegistrationFixture.Path, registration.ToJsonString());
        var report = Path.Combine(root, CommonExecutionEvidence.ReportPath);
        var candidateSnapshot = CommonExecutionEvidence.Snapshot(root);
        RawLeanReportArtifact.WriteFile(report, candidateSnapshot, template
            ? TemplateReport(candidateSnapshot, fixture.Reports, scenario == "template-missing-evidence") : LeanAxiomReport.Create(fixture.Reports));
        foreach (var suffix in new[] { ".sha256", ".input.attestation", ".provenance.json" })
            File.WriteAllText(report + suffix, "synthetic producer sidecar\n");
        var environment = new ProductionCliEnvironment(root, new GitRepositoryGateway(root), new FakeLeanReportSource(null));
        var currentConsole = new BufferedConsole();
        var currentExit = CliApplication.Run(["check-current", "--candidate-lean-report", report], environment, currentConsole);
        Assert.True(currentExit == 0, currentConsole.Output + currentConsole.Error);
        if (scenario == "annotation")
        {
            using var currentJson = JsonDocument.Parse(currentConsole.Output);
            Assert.Contains(currentJson.RootElement.GetProperty("skipped").EnumerateArray(),
                rule => rule.GetString() == "SL-022");
            Assert.DoesNotContain(currentJson.RootElement.GetProperty("diagnostics").EnumerateArray(),
                finding => finding.GetProperty("RuleId").GetProperty("Value").GetString() == "SL-022");
        }
        const string log = CommonExecutionEvidence.RootPath + "/unit-stage.log";
        Write(log, "fixture common stage succeeded\n");
        var registered = EngineeringProjectRegistry.Read(CommonExecutionEvidence.Snapshot(root)).Projects.Where(project => project.Ci).ToArray();
        var inventory = registered.Select(project => new BuiltTestProject(project.Path, "build/ci/bin/" + project.Assembly + ".dll")).ToArray();
        foreach (var test in inventory) Write(test.Assembly, "synthetic runtime");
        CommonExecutionEvidence.Write(root, CommonBuildOutputs.TestsPath, inventory);
        var runtimeFiles = new List<string>();
        if (staged)
        {
            var runtime = Path.GetDirectoryName(Path.Combine(root, CommonExecutionEvidence.CliPath))!;
            Directory.CreateDirectory(runtime);
            foreach (var file in Directory.GetFiles(Path.GetDirectoryName(typeof(StrataLint.Cli.Program).Assembly.Location)!))
            {
                var destination = Path.Combine(runtime, Path.GetFileName(file));
                File.Copy(file, destination);
                var relative = Path.GetRelativePath(root, destination).Replace('\\', '/');
                if (defect != "unbound-dll" || relative != CommonExecutionEvidence.CliPath) runtimeFiles.Add(relative);
            }
        }
        var build = CommonExecutionEvidence.SealBuild(root, CommonExecutionEvidence.Candidate(root), inventory.Select(test => test.Assembly).Append(CommonBuildOutputs.TestsPath).Append(log).Concat(runtimeFiles),
            CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", log)).ToArray());
        Assert.Equal(0, StrataLint.EngineeringScope.Program.RunCurrentTests(root, (project, results) =>
        {
            var assembly = registered.Single(row => row.Path == project).Assembly;
            File.WriteAllText(Path.Combine(results, "run.trx"), $$"""
                <TestRun><Results><UnitTestResult testId="one" testName="Fixture.Runs" outcome="Passed" /></Results>
                <TestDefinitions><UnitTest id="one" storage="{{assembly}}.dll"><TestMethod className="Fixture" name="Runs" /></UnitTest></TestDefinitions>
                <ResultSummary outcome="Completed"><Counters executed="1" passed="1" failed="0" /></ResultSummary></TestRun>
                """);
            return 0;
        }, TextWriter.Null, build));
        SealChecks("engineering");
        CommonExecutionEvidence.SealEngineering(root, build, CommonExecutionEvidence.EngineeringSteps.Select(name => new StageStep(name, name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", log)).ToArray());
        if (scenario == "reused")
        {
            Assert.True(CommonExecutionEvidence.ExportTestSeed(root, TextWriter.Null));
            var original = CommonExecutionEvidence.ValidateTests(root);
            build = CommonExecutionEvidence.SealBuild(root, build.Candidate, build.Materials.Select(material => material.Path), build.Steps);
            Assert.Equal(0, StrataLint.EngineeringScope.Program.RunCurrentTests(root, (_, _) => throw new InvalidOperationException("equal inputs must reuse"), TextWriter.Null, build));
            Assert.Equal(original.Projects.Select(row => row with { Status = "reused" }), CommonExecutionEvidence.ValidateTests(root).Projects);
            SealChecks("engineering");
        CommonExecutionEvidence.SealEngineering(root, build, CommonExecutionEvidence.EngineeringSteps.Select(name => new StageStep(name, name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", log)).ToArray());
        }
        SealChecks("current");
        CommonExecutionEvidence.SealCurrent(root, build, CommonExecutionEvidence.CurrentSteps.Select(name => new StageStep(name, 0, 0, "executed", log)).ToArray());
        void SealChecks(string stage)
        {
            var checks = CommonExecutionEvidence.BeginChecks(root, stage, build, TextWriter.Null);
            foreach (var id in checks.Ids)
                checks.Run(id, () => new CheckWork(id switch
                {
                    "selftest-pair" => [new("selftest-first", 0, "SELFTEST PASS\n"), new("selftest-second", 0, "SELFTEST PASS\n")],
                    "capability-proof" => [new("restore-CompileFailProof", 0, "restored"), new(id, 1, "MissingCapability.cs(13,9): error CS7036: missing metaClear\n")],
                    "banned-api-proof" => [new("restore-BannedApiCompileFailProof", 0, "restored"), new(id, 1, "BannedApiViolations.cs(1,1): error RS0030: banned symbol\n")],
                    _ => [new(id, 0, id.StartsWith("SL-", StringComparison.Ordinal) ? CommonCheckRegistrationFixture.Predicate(id) : "passed")],
                }, id == "scribe-describe" ? VerifiedScribeEmissions.Create(CommonExecutionEvidence.Snapshot(root).Files.Values
                    .Where(file => file.Path.Value.StartsWith("Blueprint/", StringComparison.Ordinal) && file.Path.Value.EndsWith(".scribe.cs", StringComparison.Ordinal))
                    .Select(file => new ScribeEmissionRecord(file.Path.Value["Blueprint/".Length..^".scribe.cs".Length], file.Path.Value,
                        DigestionFingerprint.Compute(file.RawBytes.AsSpan()).RawSha256,
                        file.Path.Value[..^".scribe.cs".Length] + ".md", "sha256:" + new string('a', 64)))).WriteMaterial() : null));
            checks.Seal();
        }
        if (afterValid)
        {
            var accepted = environment.CheckDelta(["--protected-base", basis, "--candidate-lean-report", report]);
            Assert.True(accepted.ExitCode == 0, accepted.Output + accepted.Error);
            AssertAcceptedBaseTests(accepted.Output);
        }
        switch (defect)
        {
            case "missing-report": File.Delete(report); break;
            case "invalid-report": File.WriteAllText(report, "not JSON"); break;
            case "missing-report-archive": File.Delete(report + ".materials.zip"); break;
            case "stale-report": File.AppendAllText(Path.Combine(root, RuleFixture.RingPath), "-- changed source\n"); break;
            case "current-round":
            case "unbound-report-archive":
            case "contradictory-material":
                var evidence = CommonExecutionEvidence.Read<CommonStageRecord>(root, CommonExecutionEvidence.CurrentPath);
                CommonExecutionEvidence.Write(root, CommonExecutionEvidence.CurrentPath, defect switch
                {
                    "current-round" => evidence with { Round = "another-round" },
                    "unbound-report-archive" => evidence with
                    {
                        Materials = evidence.Materials.Where(material => material.Path != CommonExecutionEvidence.ReportPath + ".materials.zip").ToArray(),
                    },
                    _ => evidence with
                    {
                        // This operation log is also bound by build and engineering.
                        // Sharing validated bytes must still compare each claimed digest.
                        Materials = evidence.Materials.Select(material => material.Path == log
                            ? material with { Sha256 = new string('0', 64) } : material).ToArray(),
                    },
                });
                break;
            case "missing-current": File.Delete(Path.Combine(root, CommonExecutionEvidence.CurrentPath)); break;
            case "invalid-dll": File.AppendAllText(Path.Combine(root, CommonExecutionEvidence.CliPath), "damage"); break;
            case "candidate-mismatch": File.AppendAllText(Path.Combine(root, RuleFixture.BlueprintPath), "new round\n"); break;
            case "failed-trx":
                var trx = Directory.GetFiles(Path.Combine(root, CommonExecutionEvidence.RootPath), "*.trx", SearchOption.AllDirectories).First();
                File.WriteAllText(trx, TemporaryFileSystem.File.ReadAllText(trx).Replace("Passed", "Failed", StringComparison.Ordinal));
                break;
        }
        var console = new BufferedConsole();
        var hashes = CommonExecutionEvidence.Read<TestExecutionRecord>(root, CommonExecutionEvidence.TestsPath).Materials
            .ToDictionary(material => Path.GetFullPath(Path.Combine(root, material.Path)), _ => 0, StringComparer.Ordinal);
        var previousHashing = CommonExecutionEvidence.Hashing.Value;
        var previousReading = RawLeanReportArtifact.Reading.Value;
        var parentReportReads = 0;
        int exit;
        try
        {
            CommonExecutionEvidence.Hashing.Value = path => { if (hashes.ContainsKey(path)) hashes[path]++; };
            RawLeanReportArtifact.Reading.Value = () => parentReportReads++;
            if (staged)
            {
                using var output = new StringWriter();
                exit = new CommonStages(root, output).Run("delta", basis);
                console.WriteOutput(output.ToString());
            }
            else exit = CliApplication.Run(["check-delta", "--protected-base", basis, "--candidate-lean-report", report], environment, console);
        }
        finally
        {
            CommonExecutionEvidence.Hashing.Value = previousHashing;
            RawLeanReportArtifact.Reading.Value = previousReading;
        }
        Assert.True(exit == expectedExit, $"expected exit {expectedExit}, got {exit}: {console.Output}{console.Error}");
        Assert.Contains(diagnostic, console.Output + console.Error, StringComparison.Ordinal);
        if (scenario == "template-unchanged")
            Assert.DoesNotContain("DTR-", console.Output + console.Error, StringComparison.Ordinal);
        if (scenario is "valid" or "reused")
        {
            Assert.All(hashes, row => Assert.Equal(1, row.Value));
            AssertAcceptedBaseTests(console.Output);
        }
        void AssertAcceptedBaseTests(string output)
        {
            using var verdict = JsonDocument.Parse(output);
            Assert.Equal(CommonExecutionEvidence.Read<TestExecutionRecord>(root, CommonExecutionEvidence.TestsPath).Projects
                .Select(row => (row.Project, row.Status, row.ExecutionCandidate, row.ExecutionRound)),
                verdict.RootElement.GetProperty("accepted_base_tests").EnumerateArray().Select(row => (
                    row.GetProperty("project").GetString()!, row.GetProperty("status").GetString()!,
                    row.GetProperty("execution_candidate").GetString()!, row.GetProperty("execution_round").GetString()!)));
        }
        if (staged)
        {
            // The real candidate CLI owns common acceptance; its parent authenticates
            // the runtime before launching it and retains the child's failure code.
            var launches = defect is not ("invalid-dll" or "unbound-dll" or "candidate-mismatch");
            using var summary = JsonDocument.Parse(File.ReadAllText(Path.Combine(root, "build/ci/delta-result.json")));
            var steps = summary.RootElement.GetProperty("steps").EnumerateArray().ToArray();
            Assert.Equal(launches ? 1 : 0, steps.Length);
            if (launches) Assert.Equal(expectedExit, steps[0].GetProperty("raw_exit").GetInt32());
            Assert.Equal(0, parentReportReads);
            Assert.All(hashes, row => Assert.Equal(0, row.Value));
        }
        if (scenario is "missing-base-project" or "premanifest-missing-base-project" or "original-registration-missing-base-project")
        {
            Assert.Contains($"ENGINEERING_TEST_PROJECT_REMOVED project={JsonSerializer.Serialize(firstProject)}",
                console.Output, StringComparison.Ordinal);
            Assert.Contains($"base test project has no current accepted-success coverage: {firstProject}",
                console.Error, StringComparison.Ordinal);
        }
        if (scenario == "annotation")
        {
            Assert.Empty(console.Error);
            using var json = JsonDocument.Parse(console.Output);
            Assert.Contains(json.RootElement.GetProperty("executed").EnumerateArray(),
                rule => rule.GetString() == "SL-022");
            var finding = Assert.Single(json.RootElement.GetProperty("diagnostics").EnumerateArray(),
                diagnostic => diagnostic.GetProperty("RuleId").GetProperty("Value").GetString() == "SL-022");
            Assert.Equal(protectedPath, finding.GetProperty("Path").GetString());
            Assert.Equal((int)AdmissionEffect.HumanGate, finding.GetProperty("AdmissionEffect").GetInt32());
            Assert.Equal("protected-surface change detected (SL-022)", finding.GetProperty("Message").GetString());
        }

        void Write(string path, string text)
        {
            var full = Path.Combine(root, path);
            Directory.CreateDirectory(Path.GetDirectoryName(full)!);
            File.WriteAllText(full, text);
        }
    }
}
