using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class CommonCheckExecutionTests
{
    [Theory]
    [InlineData("report", 1)]
    [InlineData("report-materials", 1)]
    [InlineData("report-missing", 1)]
    [InlineData("candidate", 22)]
    [InlineData("round", 22)]
    [InlineData("null-unit", 1)]
    public void CurrentSeedReportAndAcceptanceDamageCannotSupplyStaleMaterial(string damage, int expected)
    {
        using var fixture = new Fixture();
        fixture.Tree.Write("Meta/ReportProducers/check.json", "{\"schema\":\"report-producer-scope-v1\",\"scripts\":[],\"projects\":[],\"materials\":[\"global.json\"]}");
        var manifestPath = Path.Combine(fixture.Tree.Root, CommonExecutionEvidence.CheckManifestPath);
        var manifest = JsonNode.Parse(File.ReadAllText(manifestPath))!;
        manifest["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == "SL-001")!["report_inputs"] = JsonNode.Parse("[{\"producer\":\"Meta/ReportProducers/check.json\",\"artifact\":\"raw-lean-report\",\"materials\":[\"global.json\"]}]");
        File.WriteAllText(manifestPath, manifest.ToJsonString());
        fixture.Tree.Track();
        var build = fixture.Tree.Build();
        CiTransportTests.Report(fixture.Tree.Root);
        var original = Run();
        CommonExecutionEvidence.SealCurrent(fixture.Tree.Root, build, CommonExecutionEvidence.CurrentSteps.Select(name => new StageStep(name, 0, 0, "executed", "build/ci/fixture-build.log")).ToArray());
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Tree.Root, "current", TextWriter.Null));
        var seed = Path.Combine(fixture.Tree.Root, CommonExecutionEvidence.CheckSeedPath("current"));
        var path = Path.Combine(seed, "checks.json");
        var doc = JsonNode.Parse(File.ReadAllText(path))!;
        var unit = doc["units"]![0]!;
        if (damage == "report") File.WriteAllText(Path.Combine(seed, unit["report"]!.ToString()), "broken");
        if (damage == "report-materials") File.WriteAllText(Path.Combine(seed, unit["report"] + ".materials.zip"), "broken");
        if (damage == "report-missing") unit["report"] = null;
        if (damage == "candidate") doc["candidate"] = new string('0', 64);
        if (damage == "round") doc["round"] = new string('0', 32);
        if (damage == "null-unit") doc["units"]![0] = null;
        File.WriteAllText(path, doc.ToJsonString());
        var calls = 0;
        Run(() => calls++);
        Assert.Equal(expected, calls);
        CommonCheckRecord Run(Action? executed = null)
        {
            var checks = CommonExecutionEvidence.BeginChecks(fixture.Tree.Root, "current", build, TextWriter.Null);
            foreach (var id in checks.Ids) checks.Run(id, () =>
            {
                executed?.Invoke();
                return new CheckWork([new(id, 0, id.StartsWith("SL-", StringComparison.Ordinal) ? id == "SL-003" ? "{\"rule\":\"SL-003\",\"diagnostics\":[{\"rule\":\"SL-003\",\"title\":\"Capacity pressure\",\"severity\":1,\"effect\":0,\"path\":\"fixtures/selftest.txt\",\"message\":\"original observation\"}]}"
                    : CommonCheckRegistrationFixture.Predicate(id) : "passed")],
                    id == "scribe-describe" ? CommonCheckRegistrationFixture.ScribeMaterial : null);
            });
            return checks.Seal();
        }
    }

    [Fact]
    public void OptionalSeedUsesExistingTransportAndImportsAfterCandidateChanges()
    {
        using var fixture = new Fixture();
        var original = fixture.Run();
        fixture.Seed();
        SharedBuildContractTests.Git(fixture.Tree.Root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qam", "registered checks");
        var commit = SharedBuildContractTests.Git(fixture.Tree.Root, "rev-parse", "HEAD");
        var archive = Path.Combine(fixture.Tree.Root, "build/optional.tgz");
        using var output = new StringWriter();
        string[] Options(string action) => [action, "--repository", fixture.Tree.Root, "--stage", "engineering-seed", "--commit", commit, "--run-id", "17", "--run-attempt", "2"];
        Assert.Equal(0, Program.Run([.. Options("transport-pack"), "--archive", archive], TestResultEvidence.Load, output, output));
        Assert.Contains(CommonExecutionEvidence.TestSeedPath + "/tests.json", File.ReadAllText(Path.Combine(fixture.Tree.Root, CommonExecutionEvidence.BundleListPath("engineering-seed"))), StringComparison.Ordinal);
        Directory.Delete(Path.Combine(fixture.Tree.Root, CommonExecutionEvidence.CheckSeedPath("engineering")), true);
        Directory.Delete(Path.Combine(fixture.Tree.Root, CommonExecutionEvidence.TestSeedPath), true);
        using (var stream = File.OpenRead(archive))
        using (var gzip = new System.IO.Compression.GZipStream(stream, System.IO.Compression.CompressionMode.Decompress))
            System.Formats.Tar.TarFile.ExtractToDirectory(gzip, fixture.Tree.Root, overwriteFiles: true);
        fixture.Tree.Write("unrelated.txt", "new candidate");
        fixture.Tree.Track();
        SharedBuildContractTests.Git(fixture.Tree.Root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qam", "unrelated");
        Assert.Equal(0, Program.Run(Options("transport-verify"), TestResultEvidence.Load, output, output));
        Assert.Equal(0, Program.Run(["check-seed-import", "--repository", fixture.Tree.Root, "--stage", "engineering"], TestResultEvidence.Load, output, output));
        var current = fixture.Run();
        Assert.Empty(fixture.Calls);
        Assert.Equal(original.Units.Select(unit => unit.ExecutionRound), current.Units.Select(unit => unit.ExecutionRound));
    }

    [Theory]
    [InlineData("candidate")]
    [InlineData("round")]
    [InlineData("material")]
    public void MalformedCurrentResultCannotExportASeed(string damage)
    {
        using var fixture = new Fixture();
        fixture.Run();
        fixture.Seed();
        var path = Path.Combine(fixture.Tree.Root, CommonExecutionEvidence.ChecksPath("engineering"));
        var doc = JsonNode.Parse(File.ReadAllText(path))!;
        if (damage == "candidate") doc["candidate"] = new string('0', 64);
        if (damage == "round") doc["round"] = new string('0', 32);
        if (damage == "material") File.AppendAllText(Path.Combine(fixture.Tree.Root, doc["units"]![0]!["operations"]![0]!["log"]!.ToString()), "changed");
        else File.WriteAllText(path, doc.ToJsonString());
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ExportCheckSeed(fixture.Tree.Root, "engineering", TextWriter.Null));
    }

    [Fact]
    public void CurrentColdThenWarmRunsZeroOfTwentyTwoUnitsAndOneChangedPredicateRunsAlone()
    {
        using var fixture = new Fixture();
        var path = Path.Combine(fixture.Tree.Root, CommonExecutionEvidence.CheckManifestPath);
        var doc = JsonNode.Parse(File.ReadAllText(path))!;
        doc["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == "SL-015")!["materials"] = new JsonArray("fixtures/selftest.txt");
        File.WriteAllText(path, doc.ToJsonString());
        fixture.Tree.Track();
        fixture.Tree.Build();
        CiTransportTests.Report(fixture.Tree.Root);
        var calls = new List<string>();
        void Run()
        {
            calls.Clear();
            var build = fixture.Tree.Build();
            var checks = CommonExecutionEvidence.BeginChecks(fixture.Tree.Root, "current", build, TextWriter.Null);
            foreach (var id in checks.Ids) checks.Run(id, () =>
            {
                calls.Add(id);
                return new CheckWork([new(id, 0, id.StartsWith("SL-", StringComparison.Ordinal)
                    ? id == "SL-003" ? "{\"rule\":\"SL-003\",\"diagnostics\":[{\"rule\":\"SL-003\",\"title\":\"Capacity pressure\",\"severity\":1,\"effect\":0,\"path\":\"fixtures/selftest.txt\",\"message\":\"original observation\"}]}"
                    : CommonCheckRegistrationFixture.Predicate(id) : "passed")],
                    id == "scribe-describe" ? CommonCheckRegistrationFixture.ScribeMaterial : null);
            });
            checks.Seal();
            CommonExecutionEvidence.SealCurrent(fixture.Tree.Root, build, CommonExecutionEvidence.CurrentSteps.Select(name => new StageStep(name, 0, 0, "executed", "build/ci/fixture-build.log")).ToArray());
        }
        Run();
        Assert.Equal(22, calls.Count);
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Tree.Root, "current", TextWriter.Null));
        Run();
        Assert.Empty(calls);
        var warm = CommonExecutionEvidence.ValidateChecks(fixture.Tree.Root, "current", CommonExecutionEvidence.ValidateBuild(fixture.Tree.Root));
        var observation = warm.Units.Single(unit => unit.Id == "SL-003");
        Assert.Contains("original observation", File.ReadAllText(Path.Combine(fixture.Tree.Root, observation.Operations.Single().Log)), StringComparison.Ordinal);
        fixture.Tree.Write("fixtures/selftest.txt", "changed");
        fixture.Tree.Track();
        Run();
        Assert.Equal(new[] { "SL-015" }, calls);
    }

    [Fact]
    public void ColdThenTwoWarmCyclesKeepOriginalOutputsAndExecuteZeroUnits()
    {
        using var fixture = new Fixture();
        var first = fixture.Run();
        Assert.Equal(3, fixture.Calls.Count);
        for (var cycle = 0; cycle < 2; cycle++)
        {
            fixture.Seed();
            fixture.Tree.Write("unrelated.txt", cycle.ToString());
            fixture.Tree.Track();
            var warm = fixture.Run();
            Assert.Empty(fixture.Calls);
            Assert.NotEqual(first.Candidate, warm.Candidate);
            Assert.All(warm.Units, unit =>
            {
                var original = first.Units.Single(row => row.Id == unit.Id);
                Assert.Equal("reused", unit.Status);
                Assert.Equal(original.ExecutionCandidate, unit.ExecutionCandidate);
                Assert.Equal(original.ExecutionRound, unit.ExecutionRound);
                Assert.Equal(original.Operations, unit.Operations);
                Assert.Equal(original.Materials, unit.Materials);
            });
        }
    }

    [Theory]
    [InlineData("source")]
    [InlineData("mode")]
    [InlineData("member")]
    public void OneDeclaredInputInvalidatesOnlyItsUnit(string change)
    {
        using var fixture = new Fixture();
        fixture.Run();
        fixture.Seed();
        if (change == "source") fixture.Tree.Write("fixtures/selftest.txt", "changed");
        if (change == "member") fixture.Tree.Write("fixtures/new.txt", "new");
        if (change == "mode" && !OperatingSystem.IsWindows())
            File.SetUnixFileMode(Path.Combine(fixture.Tree.Root, "fixtures/selftest.txt"), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        fixture.Tree.Track();
        fixture.Run();
        Assert.Equal(change == "mode" && OperatingSystem.IsWindows() ? [] : new[] { "selftest-pair" }, fixture.Calls);
    }

    [Theory]
    [InlineData("absent", 3)]
    [InlineData("corrupt", 3)]
    [InlineData("second-output", 1)]
    [InlineData("proof-log", 1)]
    [InlineData("proof-exit", 1)]
    [InlineData("proof-marker", 1)]
    public void UntrustedSeedDamageExecutesRequiredUnit(string damage, int expected)
    {
        using var fixture = new Fixture();
        var original = fixture.Run();
        if (damage != "absent") fixture.Seed();
        var seed = Path.Combine(fixture.Tree.Root, CommonExecutionEvidence.CheckSeedPath("engineering"));
        if (damage == "corrupt") File.WriteAllText(Path.Combine(seed, "checks.json"), "broken");
        if (damage is "second-output" or "proof-log")
        {
            var unit = original.Units.Single(row => row.Id == (damage == "second-output" ? "selftest-pair" : "capability-proof"));
            File.Delete(Path.Combine(seed, unit.Operations.Last().Log));
        }
        if (damage is "proof-exit" or "proof-marker")
        {
            var path = Path.Combine(seed, "checks.json");
            var doc = JsonNode.Parse(File.ReadAllText(path))!;
            var unit = doc["units"]!.AsArray().Single(row => row!["id"]!.ToString() == "banned-api-proof")!;
            if (damage == "proof-exit") unit["operations"]![1]!["raw_exit"] = 0;
            else
            {
                var log = unit["operations"]![1]!["log"]!.ToString();
                File.WriteAllText(Path.Combine(seed, log), "Build FAILED.\n");
                unit["materials"]!.AsArray().Single(material => material!["path"]!.ToString() == log)!["sha256"] = CommonExecutionEvidence.Hash(Path.Combine(seed, log));
            }
            File.WriteAllText(path, doc.ToJsonString());
        }
        fixture.Run();
        Assert.Equal(expected, fixture.Calls.Count);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("duplicate")]
    [InlineData("dangling")]
    [InlineData("conflicting")]
    public void RegistrationErrorsNameObjectBeforeExecution(string defect)
    {
        using var fixture = new Fixture();
        var path = Path.Combine(fixture.Tree.Root, CommonExecutionEvidence.CheckManifestPath);
        var doc = JsonNode.Parse(File.ReadAllText(path))!;
        var rows = doc["checks"]!.AsArray();
        var row = rows.Single(row => row!["id"]!.ToString() == "selftest-pair")!;
        if (defect == "missing") rows.Remove(row);
        if (defect == "duplicate") rows.Add(row.DeepClone());
        if (defect == "dangling") row["materials"] = new JsonArray("absent.txt");
        if (defect == "conflicting") row["material_excludes"] = new JsonArray("fixtures/selftest.txt");
        File.WriteAllText(path, doc.ToJsonString());
        var error = Assert.Throws<InvalidDataException>(() => fixture.Run());
        Assert.Contains("selftest-pair", error.Message, StringComparison.Ordinal);
        Assert.Empty(fixture.Calls);
    }

    [Theory]
    [InlineData("exit")]
    [InlineData("different-pair")]
    [InlineData("unknown-error")]
    [InlineData("missing-marker")]
    public void SelectedFailureNeverUsesStaleSuccess(string failure)
    {
        using var fixture = new Fixture();
        fixture.Run();
        fixture.Seed();
        fixture.Tree.Write(failure is "unknown-error" or "missing-marker"
            ? "tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs" : "fixtures/selftest.txt", "// banned-api-proof\n// changed");
        if (failure is "unknown-error" or "missing-marker")
        {
            var manifest = Path.Combine(fixture.Tree.Root, CommonExecutionEvidence.CheckManifestPath);
            var doc = JsonNode.Parse(File.ReadAllText(manifest))!;
            doc["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == "banned-api-proof")!["materials"] = new JsonArray("tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs");
            File.WriteAllText(manifest, doc.ToJsonString());
        }
        fixture.Tree.Track();
        Assert.Throws<InvalidDataException>(() => fixture.Run(failure));
        Assert.False(File.Exists(Path.Combine(fixture.Tree.Root, CommonExecutionEvidence.ChecksPath("engineering"))));
    }

    internal sealed class Fixture : IDisposable
    {
        internal CurrentExecutionContractTests.CandidateFixture Tree { get; } = new();
        internal List<string> Calls { get; } = [];
        internal Fixture()
        {
            Tree.RegisterProofs();
            Tree.Write("global.json", "{\"sdk\":{\"version\":\"10.0.103\"}}");
            Tree.Write("tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs", "// banned-api-proof\n");
            Tree.Write("fixtures/selftest.txt", "selftest");
            var ids = new[] { "SL-001", "SL-002", "SL-003", "SL-004", "SL-006", "SL-008", "SL-010", "SL-011", "SL-012", "SL-015", "SL-017", "SL-018", "SL-019", "SL-020", "SL-021", "SL-023", "SL-025", "SL-026", "selftest-pair", "capability-proof", "banned-api-proof", "scribe-projections", "scribe-describe", "scribe-markdown", "filemap" };
            CommonExecutionEvidence.Write(Tree.Root, CommonExecutionEvidence.CheckManifestPath,
                new CommonCheckManifest("ci-check-input-registration-v1", ids.Select(id => new RegisteredCommonCheck(id,
                    [CurrentExecutionContractTests.CandidateFixture.First], id == "selftest-pair" ? ["fixtures/selftest.txt", "fixtures/*.txt"] : [], [], [], [])).ToArray()));
            Tree.Track();
        }
        internal CommonCheckRecord Run(string? failure = null)
        {
            Calls.Clear();
            var build = Tree.Build();
            var session = CommonExecutionEvidence.BeginChecks(Tree.Root, "engineering", build, TextWriter.Null);
            foreach (var id in session.Ids)
                session.Run(id, () =>
                {
                    Calls.Add(id);
                    var ops = Work(id);
                    if (failure == "exit") ops[0] = ops[0] with { RawExit = 1 };
                    if (failure == "different-pair") ops[^1] = ops[^1] with { Output = "different" };
                    if (failure == "unknown-error") ops[^1] = ops[^1] with { Output = ops[^1].Output + "\nx.cs(2,1): error CS9999: unexpected" };
                    if (failure == "missing-marker") ops[^1] = ops[^1] with { Output = "" };
                    return new CheckWork(ops);
                });
            return session.Seal();
        }
        internal void Seed()
        {
            var build = CommonExecutionEvidence.ValidateBuild(Tree.Root);
            Xunit.Assert.Equal(0, Program.RunCurrentTests(Tree.Root, (_, directory) => { Tree.WriteTrx(directory, "Passed"); return 0; }, TextWriter.Null, build));
            const string log = "build/ci/fixture-build.log";
            CommonExecutionEvidence.SealEngineering(Tree.Root, build, [new("tests", 0, 0, "executed", log)]);
            Xunit.Assert.True(CommonExecutionEvidence.ExportCheckSeed(Tree.Root, "engineering", TextWriter.Null));
        }
        internal static CheckOperation[] Work(string id) => id switch
        {
            "selftest-pair" => [new("selftest-first", 0, "SELFTEST PASS\n"), new("selftest-second", 0, "SELFTEST PASS\n")],
            "capability-proof" => [new("restore-CompileFailProof", 0, "restored"), new(id, 1, "MissingCapability.cs(13,9): error CS7036: missing metaClear\n")],
            "banned-api-proof" => [new("restore-BannedApiCompileFailProof", 0, "restored"), new(id, 1, "BannedApiViolations.cs(1,1): error RS0030: banned symbol\n")],
            _ => [new(id, 0, "passed")],
        };
        public void Dispose() => Tree.Dispose();
    }
}
