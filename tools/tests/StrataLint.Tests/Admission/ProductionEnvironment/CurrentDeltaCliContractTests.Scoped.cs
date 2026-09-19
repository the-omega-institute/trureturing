using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;

namespace StrataLint.Tests;

public sealed partial class CurrentDeltaCliContractTests
{
    [Theory]
    [InlineData("template", 3, "SL-022")]
    [InlineData("staged-template", 0, "SL-022")]
    [InlineData("staged-metadata", 0, "SL-016")]
    [InlineData("template-overlimit", 1, "SL-003")]
    [InlineData("template-warm-overlimit", 1, "SL-003")]
    [InlineData("template-warm-overlimit", 1, "SL-003", "CLAUDE.md", "CLAUDE.md")]
    [InlineData("template-warm-overlimit", 1, "SL-003", "agents/prover.md", "agents/**")]
    [InlineData("template-warm-overlimit", 1, "SL-003", "skills/codex-formal-answer/SKILL.md", "skills/**")]
    [InlineData("template-warm-overlimit", 1, "SL-003", "tools/scripts/agent/merge-gate.sh", "tools/scripts/agent/merge-gate.sh")]
    [InlineData("template-warm-overlimit", 1, "SL-003", "tools/scripts/agent/openproblem/erdos617.py", "tools/scripts/agent/openproblem/erdos617.py")]
    [InlineData("template-warm-overlimit", 1, "SL-003", "tools/tests/BannedApiCompileFailProof/CapacityProbe.cs", "tools/tests/**/*.cs")]
    [InlineData("metadata", 0, "SL-016")]
    [InlineData("metadata-invalid", 1, "SL-016")]
    [InlineData("metadata-missing-report", 2, "raw-lean-report.json")]
    [InlineData("metadata-stale-report", 2, "source")]
    [InlineData("engineering-mixed", 2, "tests.json")]
    [InlineData("content-mixed", 1, "SL-029")]
    [InlineData("missing-current", 2, "current.json")]
    [InlineData("candidate-mismatch", 2, "candidate identity")]
    [InlineData("missing-round", 2, "build round")]
    [InlineData("missing-plan-options", 2, "requires a common plan and changes")]
    [InlineData("wrong-round", 2, "round mismatch")]
    [InlineData("wrong-base", 2, "base matching its required PR resource plan")]
    [InlineData("forged-plan", 2, "missing, failed, or mismatched plan")]
    [InlineData("unbound-build-plan", 2, "selection")]
    [InlineData("unbound-current-plan", 2, "selection")]
    public void ScopedDeltaConsumesOnlyItsBoundRegisteredEvidence(string scenario, int expectedExit, string diagnostic,
        string? governedPath = null, string? capacityPattern = null)
    {
        using var environmentScope = new CiFixtureEnvironment();
        using var temporary = new TemporaryDirectory();
        var root = temporary.Path;
        var staged = scenario.StartsWith("staged-", StringComparison.Ordinal);
        var metadata = (staged ? scenario["staged-".Length..] : scenario).StartsWith("metadata", StringComparison.Ordinal);
        var template = governedPath ?? "tools/scripts/agent/openproblem/templates/impl-base-brief.md";
        const string project = "tools/StrataLint.Scribe/StrataLint.Scribe.csproj";
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[CommonExecutionEvidence.CheckManifestPath] = CommonCheckRegistrationFixture.Manifest(project);
        // Project the real capacity registration onto this fixture's template input.
        // A missing declaration must reproduce unsafe warm reuse, not be filled in here.
        var capacityInputs = JsonNode.Parse(TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(CommonExecutionEvidence.CheckManifestPath)))!["checks"]!.AsArray()
            .Single(row => row!["id"]!.GetValue<string>() == "SL-003")!["materials"]!.AsArray()
            .Where(pattern => pattern!.GetValue<string>() == (capacityPattern ?? "tools/scripts/agent/openproblem/templates/*.md"))
            .Select(pattern => pattern!.DeepClone()).ToArray();
        var checkManifest = JsonNode.Parse(fixture.Files[CommonExecutionEvidence.CheckManifestPath])!;
        checkManifest["checks"]!.AsArray().Single(row => row!["id"]!.GetValue<string>() == "SL-003")!["materials"] = new JsonArray(capacityInputs);
        fixture.Files[CommonExecutionEvidence.CheckManifestPath] = checkManifest.ToJsonString();
        fixture.Files["global.json"] = "{\"sdk\":{\"version\":\"10.0.103\"}}";
        fixture.Files["tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs"] = "// proof fixture\n";
        foreach (var file in new[] { "tools/scripts/workflow/ci.py", "tools/scripts/workflow/ci_plan.py" })
            fixture.Files[file] = TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(file));
        var resources = new[] { "build", "current-data", "delta-data", "delta-metadata", "engineering", "filemap", "lean-report" };
        fixture.Files["Meta/ci-resources.json"] = JsonSerializer.Serialize(new {
            schema = "ci-resource-execution-v1", resources = resources.Select(id => new {
                id, projects = new[] { project }, checks = id == "filemap" ? new[] { "filemap" } : id == "current-data" ? ["SL-003"] : [],
                steps = id is "filemap" or "lean-report" ? new[] { id } : id == "current-data" ? ["check-current"] : [],
            }),
        });
        fixture.Files["Meta/FILEMAP.toml"] = "schema_version = 4\nresources = [\n" + string.Concat(resources.Select(id =>
            "{ id = \"" + id + "\", stage = \"" + (id.StartsWith("delta-", StringComparison.Ordinal) ? "delta" : id is "current-data" or "filemap" or "lean-report" ? "current" : id)
            + "\", owner = \"tools/scripts/workflow/ci.py\", prerequisites = " + (id == "delta-data" ? "[\"build\",\"current-data\",\"filemap\"]" : id == "delta-metadata" ? "[\"build\",\"current-data\",\"filemap\",\"lean-report\"]" : "[]")
            + ", tools = [], cache_layers = [], cache_activation = {}, materials = [\"Meta/ci-checks.json\",\"Meta/ci-resources.json\",\"Meta/engineering-projects.json\"] },\n"))
            + "]\n[residence_policy]\ncase_id = \"FIXTURE\"\ndesired = \"explicit\"\nknown_violation_count = 0\nstatus = \"closed\"\n"
            + string.Concat(fixture.Files.Keys.Append(template).Append("Meta/FILEMAP.toml").Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)
                .Select(path => path.StartsWith("D5/", StringComparison.Ordinal) || path.StartsWith("Meta/Digestion/", StringComparison.Ordinal)
                    ? Entry(path, "content", "delta-metadata") : Entry(path, "judge", path != template && path.StartsWith("tools/tests/", StringComparison.Ordinal) ? "engineering" : "delta-data")));
        foreach (var (path, content) in fixture.Files) Write(path, content);
        Write(template, "Read the source.\n");
        Write(".gitignore", "build/\n.lake/\n__pycache__/\ntools/StrataLint.Cli/bin/\n");
        Git(root, "init", "-q"); Git(root, "add", ".");
        Commit("base");
        var basis = Git(root, "rev-parse", "HEAD");
        if (metadata)
            Write(RuleFixture.FixtureBackfillAtomPath, scenario == "metadata-invalid" ? "invalid: [\n"
                : fixture.Files[RuleFixture.FixtureBackfillAtomPath] + "\n");
        else Write(template, scenario == "template-overlimit" ? Overlimit() : "Read the current source.\n");
        if (scenario == "content-mixed") Write(RuleFixture.RingPath, fixture.Files[RuleFixture.RingPath] + "\n");
        if (scenario == "engineering-mixed") Write("tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs", "// changed proof fixture\n");
        Git(root, "add", "."); Commit("candidate");
        var candidate = Git(root, "rev-parse", "HEAD");
        const string scopePath = "build/scope.json", planPath = "build/plan.json";
        RunPlanner("pr-paths", "--base", basis, "--head", basis, "--output", scopePath);
        RunPlanner("plan", "--changes", scopePath, "--output", planPath);
        var plan = ResourceExecutionPlan.Load(root, planPath, scopePath)!;
        var reportPath = Path.Combine(root, CommonExecutionEvidence.ReportPath);
        if (plan.CurrentSteps.Contains("lean-report"))
        {
            RawLeanReportArtifact.WriteFile(reportPath, CommonExecutionEvidence.Snapshot(root), LeanAxiomReport.Create(fixture.Reports));
            foreach (var suffix in new[] { ".sha256", ".input.attestation", ".provenance.json" })
                File.WriteAllText(reportPath + suffix, "fixture companion\n");
        }
        const string logPath = "build/ci/build-operation.log";
        Write(logPath, "fixture build succeeded\n");
        var materials = new List<string> { logPath };
        if (staged)
        {
            var runtime = Path.GetDirectoryName(Path.Combine(root, CommonExecutionEvidence.CliPath))!;
            Directory.CreateDirectory(runtime);
            foreach (var file in Directory.GetFiles(Path.GetDirectoryName(typeof(StrataLint.Cli.Program).Assembly.Location)!))
            {
                var destination = Path.Combine(runtime, Path.GetFileName(file));
                File.Copy(file, destination);
                materials.Add(Path.GetRelativePath(root, destination).Replace('\\', '/'));
            }
        }
        var build = CommonExecutionEvidence.SealBuild(root, CommonExecutionEvidence.Candidate(root), materials,
            CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", logPath)).ToArray(), plan.Projects, plan.Retain(root));
        var policy = RegistryLoadAssert.Accepted(RegistryLoader.Load(Encoding.UTF8.GetBytes(fixture.Files["Meta/registry.yaml"]),
            Encoding.UTF8.GetBytes(fixture.Files["Meta/domains.yaml"]))).Policy;
        var checks = CommonExecutionEvidence.BeginChecks(root, "current", build, TextWriter.Null, plan.CheckUnits);
        checks.Run("filemap", () => new([new("filemap", 0, "passed")]));
        var currentResult = checks.ExecuteCurrentPredicates(policy, null);
        if (scenario == "template-overlimit") { AssertCapacityRejected(currentResult); return; }
        Assert.DoesNotContain(Assert.IsType<RuleExecutionOutcome.Completed>(currentResult).Capability.Diagnostics, finding => finding.AdmissionEffect == AdmissionEffect.Block);
        checks.Seal();
        CommonExecutionEvidence.CompleteCurrent(root, build,
            plan.CurrentSteps.Contains("lean-report") ? [new("lean-report", 0, 0, "executed", logPath)] : [], plan);
        if (scenario == "template-warm-overlimit")
        {
            Assert.True(CommonExecutionEvidence.ExportCheckSeed(root, "current", TextWriter.Null));
            Write(template, Overlimit());
            Git(root, "add", template);
            Git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "--amend", "--no-edit", "-q");
            candidate = Git(root, "rev-parse", "HEAD");
            RunPlanner("pr-paths", "--base", basis, "--head", basis, "--output", scopePath);
            RunPlanner("plan", "--changes", scopePath, "--output", planPath);
            plan = ResourceExecutionPlan.Load(root, planPath, scopePath)!;
            build = CommonExecutionEvidence.SealBuild(root, CommonExecutionEvidence.Candidate(root), materials, build.Steps, plan.Projects, plan.Retain(root));
            var warm = CommonExecutionEvidence.BeginChecks(root, "current", build, TextWriter.Null, plan.CheckUnits);
            warm.Run("filemap", () => new([new("filemap", 0, "passed")]));
            AssertCapacityRejected(warm.ExecuteCurrentPredicates(policy, null));
            return;
        }
        switch (scenario)
        {
            case "metadata-missing-report": File.Delete(reportPath); break;
            case "metadata-stale-report": File.AppendAllText(Path.Combine(root, RuleFixture.RingPath), "-- stale report\n"); break;
            case "missing-current": File.Delete(Path.Combine(root, CommonExecutionEvidence.CurrentPath)); break;
            case "candidate-mismatch": File.AppendAllText(Path.Combine(root, template), "new candidate\n"); break;
            case "unbound-build-plan": CommonExecutionEvidence.Write(root, CommonExecutionEvidence.BuildPath, build with { Selection = null, Projects = null }); break;
            case "unbound-current-plan":
                var record = CommonExecutionEvidence.Read<CommonStageRecord>(root, CommonExecutionEvidence.CurrentPath);
                CommonExecutionEvidence.Write(root, CommonExecutionEvidence.CurrentPath, record with { Selection = null }); break;
            case "forged-plan":
                var forged = JsonNode.Parse(File.ReadAllText(Path.Combine(root, planPath)))!;
                forged["candidate"]!["commit"] = new string('a', 40);
                File.WriteAllText(Path.Combine(root, planPath), forged.ToJsonString()); break;
        }
        var arguments = new List<string> { "--protected-base", scenario == "wrong-base" ? candidate : basis };
        if (plan.CurrentSteps.Contains("lean-report")) arguments.AddRange(["--candidate-lean-report", reportPath]);
        if (scenario != "missing-round") arguments.AddRange(["--common-build-round", scenario == "wrong-round" ? "wrong-round" : build.Round]);
        if (scenario != "missing-plan-options") arguments.AddRange(["--common-plan", planPath, "--common-changes", scopePath]);
        ExplicitCommandResult result;
        if (staged)
        {
            using var output = new StringWriter();
            var exit = new CommonStages(root, output).Run("delta", basis, planPath: planPath, changesPath: scopePath);
            result = new(exit, output.ToString(), "");
        }
        else result = new ProductionCliEnvironment(root, new GitRepositoryGateway(root), new FakeLeanReportSource(null)).CheckDelta(arguments);
        log.WriteLine("SCOPED_DELTA scenario={0} exit={1}: {2}{3}", scenario, result.ExitCode, result.Output, result.Error);
        Assert.True(result.ExitCode == expectedExit, result.Output + result.Error);
        Assert.Contains(diagnostic, result.Output + result.Error, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.EngineeringPath)));
        Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.TestsPath)));
        if (scenario is "template" or "metadata" or "metadata-invalid")
        {
            using var verdict = JsonDocument.Parse(result.Output);
            Assert.Empty(verdict.RootElement.GetProperty("accepted_base_tests").EnumerateArray());
            if (!metadata)
            {
                Assert.False(Directory.Exists(Path.Combine(root, ".lake")));
                Assert.DoesNotContain(verdict.RootElement.GetProperty("executed").EnumerateArray(), rule => rule.GetString() is "SL-008" or "SL-017");
            }
        }
        void Write(string path, string content)
        {
            var full = Path.Combine(root, path);
            Directory.CreateDirectory(Path.GetDirectoryName(full)!);
            File.WriteAllText(full, content);
        }
        void Commit(string message) => Git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", message);
        void RunPlanner(string command, params string[] arguments) => RequireSuccess(TestProcessRunner.Run("python3",
            ["-B", "tools/scripts/workflow/ci.py", command, "--repository", root, "--commit", candidate, .. arguments],
            root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024));
        static string Entry(string pattern, string plane, string resource) => "\n[[files]]\npattern = \"" + pattern
            + "\"\nrequire = [\"" + resource + "\"]\nkind = \"data\"\nadmission_plane = \"" + plane
            + "\"\nproduced_by = \"none\"\nconsumed_by = [\"test\"]\nverified_by = [\"test\"]\nartifact_id = \"none\"\nruntime_disposition = \"committed-source\"\n";
        static string Overlimit() => string.Concat(Enumerable.Repeat("Read the source.\n", 1001));
        void AssertCapacityRejected(RuleExecutionOutcome outcome) => Assert.Contains(
            Assert.IsType<RuleExecutionOutcome.Completed>(outcome).Capability.Diagnostics,
            finding => finding.RuleId.Value == "SL-003" && finding.Path == template
                && finding.AdmissionEffect == AdmissionEffect.Block && finding.Message == "artifact exceeds 1000 lines");
    }
}
