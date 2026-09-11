using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.EngineeringScope;

namespace StrataLint.Tests;

public sealed class CurrentDeltaCliContractTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CurrentRunsInParentlessRemotelessRepositoryAndFindsExistingInvalidHeader(bool selected)
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Meta/ci-checks.json"] = CommonCheckRegistrationFixture.Manifest("tools/StrataLint.Scribe/StrataLint.Scribe.csproj");
        fixture.Files["global.json"] = "{\"sdk\":{\"version\":\"10.0.103\"}}";
        fixture.Files["tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs"] = "// banned-api-proof\n";
        fixture.Files["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Files["Meta/domains.yaml"] = TestRegistry.Domains;
        if (selected)
        {
            var repository = TestRepositoryLayout.FindRoot();
            foreach (var path in new[] { "tools/scripts/workflow/ci.py", "tools/scripts/workflow/ci_plan.py" })
                fixture.Files[path] = File.ReadAllText(Path.Combine(repository, path));
            fixture.Files["Meta/ci-resources.json"] = JsonSerializer.Serialize(new {
                schema = "ci-resource-execution-v1", resources = new[] {
                    new { id = "current", projects = new[] { "tools/StrataLint.Scribe/StrataLint.Scribe.csproj" },
                        checks = new[] { "SL-012" }, steps = new[] { "check-current" } } } });
            fixture.Files["Meta/FILEMAP.toml"] = """
                schema_version = 3
                resources = [
                  { id = "current", stage = "current", owner = "tools/scripts/workflow/ci.py", prerequisites = [], tools = [], cache_layers = [], materials = ["Meta/ci-checks.json", "Meta/ci-resources.json", "Meta/engineering-projects.json"] },
                ]
                [residence_policy]
                case_id = "FIXTURE"
                desired = "explicit"
                known_violation_count = 0
                status = "closed"
                [[files]]
                pattern = "**"
                require = ["current"]
                kind = "program"
                admission_plane = "judge"
                produced_by = "none"
                consumed_by = ["test"]
                verified_by = ["test"]
                artifact_id = "none"
                runtime_disposition = "committed-source"
                """ + "\n";
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
        WriteReport();
        var environment = new ProductionCliEnvironment(temporary.Path, new GitRepositoryGateway(temporary.Path), new FakeLeanReportSource(null));
        var result = environment.CheckCurrent(Arguments());
        Assert.True(result.ExitCode == 0, result.Output + result.Error);
        if (selected)
        {
            Assert.Equal(new[] { "SL-012" }, CommonExecutionEvidence.Read<CommonCheckRecord>(temporary.Path,
                CommonExecutionEvidence.ChecksPath("current")).Units.Select(unit => unit.Id));
            using var verdict = JsonDocument.Parse(result.Output[result.Output.IndexOf("{\"executed\"", StringComparison.Ordinal)..]);
            Assert.Equal(new[] { "SL-012" }, verdict.RootElement.GetProperty("executed").EnumerateArray().Select(value => value.GetString()));
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
            Assert.True(planning.ExitCode == 0, Encoding.UTF8.GetString(planning.StandardError));
            return ["--candidate-lean-report", report, "--common-build-round", build.Round, "--common-plan", plan, "--common-changes", changes];
        }

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

    private static string Git(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run("git", arguments, root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        return Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    [Theory]
    [InlineData("valid", 0, "")]
    [InlineData("reused", 0, "")]
    [InlineData("disabled-base-project", 2, "base test project")]
    [InlineData("premanifest-base", 0, "")]
    [InlineData("premanifest-missing-base-project", 2, "base test project")]
    [InlineData("original-registration-base", 0, "")]
    [InlineData("original-registration-missing-base-project", 2, "base test project")]
    [InlineData("annotation", 3, "SL-022")]
    [InlineData("mixed", 1, "SL-029")]
    [InlineData("first-freeze", 1, "SL-008")]
    [InlineData("ratchet", 1, "SL-003")]
    [InlineData("unowned-project", 1, "TEST_PROJECT_TOPOLOGY candidate introduces topology debt: missing-owned-project StrataLint.NewProduct -> StrataLint.NewProduct.Tests")]
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
        fixture.Files["Meta/ci-checks.json"] = CommonCheckRegistrationFixture.Manifest("tools/StrataLint.Scribe/StrataLint.Scribe.csproj");
        fixture.Files["global.json"] = "{\"sdk\":{\"version\":\"10.0.103\"}}";
        fixture.Files["tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs"] = "// banned-api-proof\n";
        foreach (var pair in fixture.Files) Write(pair.Key, pair.Value);
        Write(".gitignore", ".lake/\nbuild/\n");
        // Keep the exact registered rows while representing this large declaration
        // as inline tables inside the fixture's ordinary artifact capacity envelope.
        var filemap = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "Meta/FILEMAP.toml"))
            .Split("[[files]]", StringSplitOptions.None);
        var residence = filemap[0].IndexOf("[residence_policy]", StringComparison.Ordinal);
        Write("Meta/FILEMAP.toml", filemap[0][..residence] + "files = [\n" + string.Join("\n",
            filemap.Skip(1).Select(row => "  { " + string.Join(", ", row.Split('\n', StringSplitOptions.RemoveEmptyEntries)) + " },")) +
            "\n]\n" + filemap[0][residence..]);
        const string firstProject = "tools/tests/First/First.csproj";
        Write(firstProject, "<Project><PropertyGroup><IsTestProject>true</IsTestProject></PropertyGroup></Project>\n");
        Write("tools/tests/Second/Second.csproj", "<Project><PropertyGroup><IsTestProject>true</IsTestProject></PropertyGroup></Project>\n");
        var registration = JsonNode.Parse(fixture.Files[EngineeringRegistrationFixture.Path])!;
        var projects = registration["projects"]!.AsArray();
        foreach (var (path, assembly) in new[] { (firstProject, "First"), ("tools/tests/Second/Second.csproj", "Second") })
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
        const string protectedPath = "tools/scripts/probe.sh";
        Git(root, "init", "-q"); Git(root, "add", ".");
        Git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "base");
        var baseResult = TestProcessRunner.Run("git", ["rev-parse", "HEAD"], root, TestBudgets.ScriptProcessHangGuard, 1024);
        var basis = Encoding.UTF8.GetString(baseResult.StandardOutput).Trim();
        Write(EngineeringRegistrationFixture.Path, registration.ToJsonString());
        switch (scenario)
        {
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
        const string log = CommonExecutionEvidence.RootPath + "/unit-stage.log";
        Write(log, "fixture common stage succeeded\n");
        var registered = EngineeringProjectRegistry.Read(CommonExecutionEvidence.Snapshot(root)).Projects.Where(project => project.Ci).ToArray();
        var inventory = registered.Select(project => new BuiltTestProject(project.Path, "build/ci/bin/" + project.Assembly + ".dll")).ToArray();
        foreach (var test in inventory) Write(test.Assembly, "synthetic runtime");
        CommonExecutionEvidence.Write(root, CommonBuildOutputs.TestsPath, inventory);
        var build = CommonExecutionEvidence.SealBuild(root, CommonExecutionEvidence.Candidate(root), inventory.Select(test => test.Assembly).Append(CommonBuildOutputs.TestsPath).Append(log),
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
        if (scenario is "missing-base-project" or "premanifest-missing-base-project" or "original-registration-missing-base-project")
        {
            Assert.Contains($"ENGINEERING_TEST_PROJECT_REMOVED project={JsonSerializer.Serialize(firstProject)}",
                console.Output, StringComparison.Ordinal);
            Assert.Contains($"base test project has no current accepted-success coverage: {firstProject}",
                console.Error, StringComparison.Ordinal);
        }
        if (scenario == "reused")
        {
            using var json = JsonDocument.Parse(console.Output);
            Assert.All(json.RootElement.GetProperty("accepted_base_tests").EnumerateArray(), row =>
                Assert.Equal("reused", row.GetProperty("status").GetString()));
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
