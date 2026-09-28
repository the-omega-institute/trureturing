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
using Trureturing.Truth;

namespace StrataLint.CliIntegration.Tests;

public sealed partial class CurrentDeltaCliContractTests
{
    [Theory]
    [InlineData("all")]
    [InlineData("selected")]
    [InlineData("metadata")]
    [InlineData("metadata-delta-report")]
    [InlineData("metadata-scribe")]
    [InlineData("metadata-seed-miss")]
    [InlineData("metadata-required-report")]
    [InlineData("metadata-forged-candidate")]
    [InlineData("metadata-missing-registration")]
    public void CurrentHonorsRegisteredChecksInParentlessRemotelessRepository(string scenario)
    {
        var selected = scenario != "all";
        var metadata = scenario.StartsWith("metadata", StringComparison.Ordinal);
        var mixedScribe = scenario == "metadata-scribe";
        var transportReport = scenario == "metadata-delta-report" || mixedScribe;
        string[] selectedChecks = metadata && scenario != "metadata-required-report"
            ? ["SL-003", "SL-015", "SL-019", .. mixedScribe ? new[] { "scribe-projections" } : []] : ["SL-012"];
        using var ciEnvironment = new CiFixtureEnvironment();
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        if (mixedScribe)
        {
            fixture.Files["Library/Carrier/note.md"] = "Fixture library note.\n";
            foreach (var name in new[] { "pilot", "expansion" })
                fixture.Files[$"Golden/Projection/statement-projection-{name}-v1.json"] =
                    "{\"schema\":\"statement-projection-" + name + "-fixture-v1\",\"declarations\":[]}";
        }
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
            if (mixedScribe)
                registration["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == "scribe-projections")!["report_inputs"] =
                    registration["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == "SL-012")!["report_inputs"]!.DeepClone();
            fixture.Files[CommonExecutionEvidence.CheckManifestPath] = registration.ToJsonString();
            var repository = TestRepositoryLayout.FindRoot();
            foreach (var path in new[] { "tools/scripts/workflow/ci.py", "tools/scripts/workflow/ci_plan.py" })
                fixture.Files[path] = File.ReadAllText(Path.Combine(repository, path));
            var resources = new[] {
                new { id = "current", projects = new[] { "tools/StrataLint.Scribe/StrataLint.Scribe.csproj" },
                    checks = selectedChecks.Where(id => !mixedScribe || id.StartsWith("SL-", StringComparison.Ordinal)).ToArray(),
                    steps = metadata && (!transportReport || mixedScribe) ? ["check-current"] : new[] { "check-current", "lean-report" } } }.ToList();
            if (mixedScribe)
                resources.Add(new { id = "scribe", projects = new[] { "tools/StrataLint.Scribe/StrataLint.Scribe.csproj" },
                    checks = new[] { "scribe-projections" }, steps = new[] { "check-current", "lean-report" } });
            fixture.Files["Meta/ci-resources.json"] = JsonSerializer.Serialize(new { schema = "ci-resource-execution-v1", resources });
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
                mixedScribe && entry.Pattern.StartsWith("Library/", StringComparison.Ordinal) ? ["scribe"] : ["current"],
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
                new FileMapManifest(policy.ResidencePolicy, entries, policy.ArtifactKinds,
                    mixedScribe ? [current, current with { Id = "scribe" }] : [current])).AsSpan());
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
        if (!metadata || transportReport) WriteReport();
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
            Assert.Equal(transportReport, Directory.Exists(Path.Combine(temporary.Path, ".lake")));
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
            log.WriteLine("CURRENT_EVIDENCE scenario={0} exit={1} report_reads={2}: {3}{4}",
                scenario, result.ExitCode, reads, result.Output, result.Error);
            Assert.Equal(mixedScribe ? 1 : 0, reads);
            Assert.Equal(transportReport, Directory.Exists(Path.Combine(temporary.Path, ".lake")));
            if (scenario is not ("metadata" or "metadata-seed-miss" or "metadata-delta-report" or "metadata-scribe"))
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
            Assert.True(result.ExitCode == 0, "[FAIL] mixed_scribe_metadata_current_acceptance " + result.Output + result.Error);
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
                if (unit.Id == "scribe-projections") Assert.NotNull(unit.Report);
                else Assert.Null(unit.Report);
                Assert.DoesNotContain(unit.Materials, material => material.Path.StartsWith(".lake/", StringComparison.Ordinal));
            });
            var build = CommonExecutionEvidence.ValidateBuild(temporary.Path);
            var plan = ResourceExecutionPlan.Load(temporary.Path, "build/plan.json", "build/scope.json");
            _ = CommonExecutionEvidence.CompleteCurrent(temporary.Path, build, transportReport
                ? [new StageStep("lean-report", 0, 0, "executed", "build/ci/fixture-build.log")] : [], plan);
            var verified = CommonExecutionEvidence.ValidateCurrent(temporary.Path);
            Assert.Equal(build.Candidate, verified.Candidate);
            Assert.Equal(build.Round, verified.Round);
            Assert.Equal(selectedChecks, CommonExecutionEvidence.CurrentCheckIds(temporary.Path));
            Assert.Equal(transportReport, verified.Materials.Any(material => material.Path == CommonExecutionEvidence.ReportPath));
            if (mixedScribe)
            {
                Assert.True(CommonExecutionEvidence.ExportCheckSeed(temporary.Path, "current", TextWriter.Null));
                var reused = environment.CheckCurrent(Arguments());
                Assert.True(reused.ExitCode == 0, "[FAIL] mixed_scribe_metadata_reuse_acceptance " + reused.Output + reused.Error);
                Assert.Contains("COMMON_CHECK_REUSED id=scribe-projections", reused.Output, StringComparison.Ordinal);
                var warm = CommonExecutionEvidence.Read<CommonCheckRecord>(temporary.Path, CommonExecutionEvidence.ChecksPath("current"));
                Assert.Equal("reused", warm.Units.Single(unit => unit.Id == "scribe-projections").Status);
                File.AppendAllText(report, "damage after Scribe reuse");
                var rejected = environment.CheckCurrent(Arguments());
                Assert.True(rejected.ExitCode == 2, "[FAIL] mixed_scribe_rejects_damaged_report " + rejected.Output + rejected.Error);
                Assert.Contains("Raw Lean report", rejected.Error, StringComparison.Ordinal);
                return;
            }
            if (transportReport)
            {
                File.AppendAllText(report, "damage after current checks");
                Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateCurrent(temporary.Path));
            }
            return;
        }
        Assert.True(result.ExitCode == 0, result.Output + result.Error);
        if (selected)
        {
            // The invocation rebinds bytes after callbacks and at seal while
            // sharing successful semantic acceptance of this exact report.
            Assert.Equal(1, reads);
            Assert.Equal(new[] { "SL-012" }, CommonExecutionEvidence.Read<CommonCheckRecord>(temporary.Path,
                CommonExecutionEvidence.ChecksPath("current")).Units.Select(unit => unit.Id));
            using var verdict = JsonDocument.Parse(result.Output[result.Output.IndexOf("{\"executed\"", StringComparison.Ordinal)..]);
            Assert.Equal(new[] { "SL-012" }, verdict.RootElement.GetProperty("executed").EnumerateArray().Select(value => value.GetString()));
            var policy = Assert.IsType<PolicyLoadOutcome.Accepted>(RepositoryPolicyLoader.Load(
                File.ReadAllBytes(Path.Combine(temporary.Path, "Meta/FILEMAP.toml")),
                File.ReadAllBytes(Path.Combine(temporary.Path, "Meta/domains.yaml")))).Policy;
            var missingClosure = CommonExecutionEvidence.BeginChecks(temporary.Path, "current",
                CommonExecutionEvidence.ValidateBuild(temporary.Path), TextWriter.Null, ["SL-012"]);
            var absent = Assert.Throws<InvalidDataException>(() => missingClosure.ExecuteCurrentPredicates(policy, null));
            Assert.Equal("selected current checks require Lean report evidence", absent.Message);
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
        if (selected)
        {
            using var rejected = JsonDocument.Parse(result.Output[result.Output.IndexOf("{\"executed\"", StringComparison.Ordinal)..]);
            Assert.Equal(new[] { "SL-012" }, rejected.RootElement.GetProperty("executed").EnumerateArray().Select(value => value.GetString()));
            Assert.False(File.Exists(Path.Combine(temporary.Path, CommonExecutionEvidence.ChecksPath("current"))));
        }

        string[] Arguments()
        {
            if (!selected) return ["--candidate-lean-report", report];
            var root = temporary.Path;
            const string log = "build/ci/fixture-build.log";
            Directory.CreateDirectory(Path.Combine(root, "build/ci"));
            File.WriteAllText(Path.Combine(root, log), "fixture build material");
            var commit = Git(root, "rev-parse", "HEAD");
            var changedPaths = mixedScribe
                ? new[] { "Library/Carrier/note.md", fixture.Files.Keys.First(path => path.StartsWith("Meta/Digestion/backfill/", StringComparison.Ordinal)) }
                : new[] { RuleFixture.RingPath };
            var changed = changedPaths.Select(path =>
            {
                var entry = Git(root, "ls-tree", "HEAD", "--", path).Split([' ', '\t'], StringSplitOptions.RemoveEmptyEntries);
                return new { status = "A", old = (object?)null, @new = new { path, mode = entry[0], oid = entry[2] } };
            }).ToArray();
            var changes = Path.Combine(root, "build/scope.json");
            var plan = Path.Combine(root, "build/plan.json");
            File.WriteAllText(changes, JsonSerializer.Serialize(new { schema_version = 1, mode = "current",
                candidate = new { commit, tree = Git(root, "rev-parse", "HEAD^{tree}") }, @base = (string?)null, head = (string?)null,
                complete = true, change_count = changed.Length, changes = changed }));
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
            var execution = ResourceExecutionPlan.Load(root, plan, changes)!;
            var build = CommonExecutionEvidence.SealBuild(root, CommonExecutionEvidence.Candidate(root), [log],
                CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", log)).ToArray(),
                execution.Projects, execution.Retain(root, CommonExecutionEvidence.RootPath));
            return [.. metadata && !transportReport ? Array.Empty<string>() : new[] { "--candidate-lean-report", report },
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

}
