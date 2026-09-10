using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.EngineeringScope;

namespace StrataLint.Tests;

public sealed class CurrentDeltaCliContractTests
{
    [Fact]
    public void CurrentRunsInParentlessRemotelessRepositoryAndFindsExistingInvalidHeader()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Files["Meta/domains.yaml"] = TestRegistry.Domains;
        foreach (var pair in fixture.Files)
        {
            var file = Path.Combine(temporary.Path, pair.Key);
            Directory.CreateDirectory(Path.GetDirectoryName(file)!);
            File.WriteAllText(file, pair.Value);
        }
        File.WriteAllText(Path.Combine(temporary.Path, ".gitignore"), ".lake/\nbuild/\n");
        Git(temporary.Path, "init", "-q");
        Git(temporary.Path, "add", ".");
        Git(temporary.Path, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "parentless");
        var report = Path.Combine(temporary.Path, ".lake/build/stratalint/raw-lean-report.json");
        WriteReport();
        var environment = new ProductionCliEnvironment(temporary.Path, new GitRepositoryGateway(temporary.Path), new FakeLeanReportSource(null));
        var result = environment.CheckCurrent(["--candidate-lean-report", report]);
        Assert.True(result.ExitCode == 0, result.Output + result.Error);
        File.WriteAllText(Path.Combine(temporary.Path, RuleFixture.RingPath), "def invalid : Nat := 0\n");
        WriteReport();
        result = environment.CheckCurrent(["--candidate-lean-report", report]);
        Assert.Equal(1, result.ExitCode);
        Assert.Contains("SL-012", result.Output, StringComparison.Ordinal);

        void WriteReport()
        {
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(GitRepositorySnapshotReader.ReadCurrent(temporary.Path))).Snapshot;
            RawLeanReportArtifact.WriteFile(report, snapshot, LeanAxiomReport.Create(fixture.Reports));
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

    private static void Git(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run("git", arguments, root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("valid", 0, "")]
    [InlineData("annotation", 3, "SL-022")]
    [InlineData("mixed", 1, "SL-029")]
    [InlineData("first-freeze", 1, "SL-008")]
    [InlineData("ratchet", 1, "SL-003")]
    [InlineData("missing-base-project", 2, "base test project")]
    [InlineData("missing-report", 2, "")]
    [InlineData("candidate-mismatch", 2, "candidate identity")]
    [InlineData("failed-trx", 2, "artifact integrity")]
    public void DeltaConsumesValidatedCommonResultsAndEnforcesOnlyCrossTreePredicates(string scenario, int expectedExit, string diagnostic)
    {
        using var temporary = new TemporaryDirectory();
        var root = temporary.Path;
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        foreach (var pair in fixture.Files) Write(pair.Key, pair.Value);
        Write(".gitignore", ".lake/\nbuild/\n");
        Write("Meta/FILEMAP.toml", File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "Meta/FILEMAP.toml")));
        const string firstProject = "tools/tests/First/First.csproj";
        Write(firstProject, "<Project><PropertyGroup><IsTestProject>true</IsTestProject></PropertyGroup></Project>\n");
        Write("tools/tests/Second/Second.csproj", "<Project><PropertyGroup><IsTestProject>true</IsTestProject></PropertyGroup></Project>\n");
        const string protectedPath = "tools/scripts/probe.sh";
        Git(root, "init", "-q"); Git(root, "add", ".");
        Git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "base");
        var baseResult = TestProcessRunner.Run("git", ["rev-parse", "HEAD"], root, TestBudgets.ScriptProcessHangGuard, 1024);
        var basis = Encoding.UTF8.GetString(baseResult.StandardOutput).Trim();
        switch (scenario)
        {
            case "annotation": Write(protectedPath, "#!/bin/sh\nexit 0\n"); break;
            case "mixed": Write("tools/StrataLint.Cli/probe.cs", "// candidate judge\n"); Write(RuleFixture.BlueprintPath, "# changed\n"); break;
            case "first-freeze": Write("Golden/Frozen/accepted/" + new string('a', 64) + ".json", "{}\n"); break;
            case "ratchet": for (var i = 0; i <= RepositoryRules.DirectoryFileLimit; i++) Write($"docs/reports/ratchet/{i}.json", "{}\n"); break;
            case "missing-base-project": File.Delete(Path.Combine(root, firstProject)); break;
            default: Write(RuleFixture.BlueprintPath, "# changed\n"); break;
        }
        var report = Path.Combine(root, CommonExecutionEvidence.ReportPath);
        RawLeanReportArtifact.WriteFile(report, CommonExecutionEvidence.Snapshot(root), LeanAxiomReport.Create(fixture.Reports));
        foreach (var suffix in new[] { ".sha256", ".input.attestation", ".provenance.json", ".seed.json" })
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
        Assert.Equal(0, StrataLint.EngineeringScope.Program.RunCurrentTests(root, (_, results) =>
        {
            File.WriteAllText(Path.Combine(results, "run.trx"), """
                <TestRun><Results><UnitTestResult testId="one" testName="Fixture.Runs" outcome="Passed" /></Results>
                <TestDefinitions><UnitTest id="one" storage="Fixture.dll"><TestMethod className="Fixture" name="Runs" /></UnitTest></TestDefinitions>
                <ResultSummary outcome="Completed"><Counters executed="1" passed="1" failed="0" /></ResultSummary></TestRun>
                """);
            return 0;
        }, TextWriter.Null));
        const string log = CommonExecutionEvidence.RootPath + "/unit-stage.log";
        Write(log, "fixture common stage succeeded\n");
        var candidate = CommonExecutionEvidence.Read<TestExecutionRecord>(root, CommonExecutionEvidence.TestsPath).Candidate;
        CommonExecutionEvidence.SealEngineering(root, candidate, [log], CommonExecutionEvidence.EngineeringSteps.Select(name => new StageStep(name, name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", log)).ToArray());
        CommonExecutionEvidence.SealCurrent(root, CommonExecutionEvidence.CurrentSteps.Select(name => new StageStep(name, 0, 0, "executed", log)).ToArray());
        switch (scenario)
        {
            case "missing-report": File.Delete(report); break;
            case "candidate-mismatch": File.AppendAllText(Path.Combine(root, RuleFixture.BlueprintPath), "new round\n"); break;
            case "failed-trx":
                var trx = Directory.GetFiles(Path.Combine(root, CommonExecutionEvidence.RootPath), "*.trx", SearchOption.AllDirectories).First();
                File.WriteAllText(trx, TemporaryFileSystem.File.ReadAllText(trx).Replace("Passed", "Failed", StringComparison.Ordinal));
                break;
        }
        var console = new BufferedConsole();
        var exit = CliApplication.Run(["check-delta", "--protected-base", basis, "--candidate-lean-report", report], environment, console);
        Assert.True(exit == expectedExit, $"expected exit {expectedExit}, got {exit}: {console.Output}{console.Error}");
        Assert.Contains(diagnostic, console.Output + console.Error, StringComparison.Ordinal);
        if (scenario == "missing-base-project")
        {
            Assert.Contains($"ENGINEERING_TEST_PROJECT_REMOVED project={JsonSerializer.Serialize(firstProject)}",
                console.Output, StringComparison.Ordinal);
            Assert.Contains($"base test project has no successful candidate execution: {firstProject}",
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
