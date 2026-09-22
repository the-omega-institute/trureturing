using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Xml.Linq;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed partial class ResourceRouteTests(Xunit.Abstractions.ITestOutputHelper testOutput)
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CurrentRejectsDifferentBuildPlanBeforeLaunchingProducers(bool plannedBuild)
    {
        using var fixture = new ResourceFixture(["filemap"]);
        fixture.Processes(bindPlan: plannedBuild);
        using var output = new StringWriter();
        Assert.Equal(2, fixture.Run("current", output, planned: !plannedBuild));
        Assert.Contains("current requires the same resource plan as build", output.ToString(), StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/launched")));
    }

    [Fact]
    public void ScopedFileMapChecksCannotBeSealedAsUnplannedFullCurrent()
    {
        using var fixture = new ResourceFixture(["filemap"]);
        fixture.Processes(bindPlan: true);
        fixture.Report();
        var build = CommonExecutionEvidence.ValidateBuild(fixture.Root);
        CheckEvidenceFixture.Seal(fixture.Root, "current", build);
        fixture.Write("build/ci/full.log", "complete fixture operations");
        var steps = CommonExecutionEvidence.CurrentSteps.Select(name => new StageStep(name, 0, 0, "executed", "build/ci/full.log")).ToArray();
        var error = Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.SealCurrent(fixture.Root, build, steps));
        Assert.Equal("current requires the same resource plan as build", error.Message);
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath)));
    }

    [Fact]
    public void FileMapScopeReachesTheProcessAndCannotSupplyWholeTreeSeedEvidence()
    {
        using var fixture = new ResourceFixture(["filemap"]);
        fixture.Processes(bindPlan: true);
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        var scope = FileMapInspectionScope.Read(Path.Combine(fixture.Root, CommonExecutionEvidence.FileMapScopePath));
        Assert.Equal(new[] { "fixtures/selected.txt" }, scope.Paths);
        Assert.False(scope.Actors);
        using var imported = new StringWriter();
        Assert.Equal(0, CommonExecutionEvidence.CheckSeedCommand(["check-seed-import", "--repository", fixture.Root, "--stage", "current"], imported));
        Assert.Contains("COMMON_CHECK_SEED_IMPORTED stage=current units=0", imported.ToString(), StringComparison.Ordinal);
        using var warm = new StringWriter();
        Assert.True(fixture.Run("current", warm) == 0, warm.ToString());
        Assert.Single(File.ReadAllLines(Path.Combine(fixture.Root, "build/launched")));
        Assert.Equal("reused", Assert.Single(CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root,
            CommonExecutionEvidence.ChecksPath("current")).Units).Status);
    }

    [Theory]
    [InlineData("build")]
    [InlineData("engineering")]
    [InlineData("current")]
    [InlineData("delta")]
    public void NoResourceStageRetainsGitIdentityAndClearsAcceptance(string stage)
    {
        using var fixture = new ResourceFixture([]);
        if (stage == "delta") fixture.PrPlan();
        var acceptance = CommonExecutionEvidence.RootPath + "/" + stage + ".json";
        fixture.Write(acceptance, "stale");
        fixture.Write(CommonExecutionEvidence.ChecksPath(stage), "stale");
        fixture.Write(CommonExecutionEvidence.CheckSeedPath(stage) + "/keep", "optional");
        using var output = new StringWriter();
        Assert.True(fixture.Run(stage, output) == 0, output.ToString());
        var result = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/ci/" + stage + "-result.json")))!;
        testOutput.WriteLine("COMMON_NO_WORK_SUMMARY " + result.ToJsonString());
        Assert.Equal(fixture.Commit, result["git_candidate"]!["commit"]!.ToString());
        Assert.Equal("not-required", result["status"]!.ToString());
        Assert.Empty(result["steps"]!.AsArray());
        Assert.Empty(result["artifacts"]!.AsArray());
        Assert.Empty(result["not_executed"]!.AsArray());
        Assert.Equal(stage == "engineering" ? new[] { "tests", "selftest-pair", "capability-proof", "banned-api-proof" }
            : stage == "build" ? ["restore-StrataLint", "build"] : stage == "delta" ? ["check-delta"]
            : ["lean-report", "scribe", "filemap", "check-current"],
            result["not_required"]!.AsArray().Select(value => value!.ToString()));
        if (stage == "engineering")
            Assert.Equal(new[] { "not-required", "not-required", "not-required" },
                result["check_units"]!.AsArray().Select(unit => unit!["status"]!.ToString()));
        var processes = output.ToString().Split('\n').Where(line => line.StartsWith("STAGE_PROCESS ", StringComparison.Ordinal))
            .Select(line => JsonNode.Parse(line["STAGE_PROCESS ".Length..])!).ToArray();
        if (stage == "delta")
        {
            var validation = Assert.Single(processes);
            Assert.Equal("git", validation["command"]!.ToString());
            Assert.Equal(new[] { "cat-file", "-t", result["base_sha"]!.ToString() },
                validation["arguments"]!.AsArray().Select(value => value!.ToString()));
            Assert.Equal(0, validation["child_exit"]!["code"]!.GetValue<int>());
        }
        else Assert.Empty(processes);
        Assert.False(File.Exists(Path.Combine(fixture.Root, acceptance)));
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.ChecksPath(stage))));
        Assert.Equal("optional", File.ReadAllText(Path.Combine(fixture.Root, CommonExecutionEvidence.CheckSeedPath(stage), "keep")));
    }

    [Theory]
    [InlineData("filemap-hit")]
    [InlineData("filemap-miss")]
    [InlineData("lean")]
    [InlineData("lean-report")]
    public void PlannedCurrentRunsOnlyDeclaredUnits(string scenario)
    {
        var resource = scenario.StartsWith("filemap", StringComparison.Ordinal) ? "filemap" : scenario;
        using var fixture = new ResourceFixture([resource], scenario == "filemap-miss" ? "docs/unrelated.md" : "fixtures/selected.txt");
        fixture.Processes();
        if (scenario == "filemap-hit") fixture.Report();
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        var current = CommonExecutionEvidence.ValidateCurrent(fixture.Root);
        var summaryPath = Path.Combine(fixture.Root, "build/ci/current-result.json");
        var summary = JsonNode.Parse(File.ReadAllText(summaryPath))!;
        Assert.Empty(summary["not_executed"]!.AsArray());
        Assert.DoesNotContain(summary["not_required"]!.AsArray(), name => name!.ToString() == resource);
        Assert.Equal(new[] { resource }, current.Steps.Select(step => step.Name));
        var launched = File.ReadAllLines(Path.Combine(fixture.Root, "build/launched"));
        Assert.Single(launched);
        Assert.Equal(resource == "filemap" ? "dotnet filemap-conform" : "make --no-print-directory " + resource, launched[0]);
        Assert.DoesNotContain(current.Materials, material => material.Path == CommonExecutionEvidence.ReportPath && resource != "lean-report");
        if (resource == "filemap")
        {
            Assert.Equal(new[] { "filemap" }, CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root, CommonExecutionEvidence.ChecksPath("current")).Units.Select(unit => unit.Id));
            using var warm = new StringWriter();
            Assert.True(fixture.Run("current", warm) == 0, warm.ToString());
            Assert.Single(File.ReadAllLines(Path.Combine(fixture.Root, "build/launched")));
            Assert.Equal("reused", Assert.Single(CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root, CommonExecutionEvidence.ChecksPath("current")).Units).Status);
            summary = JsonNode.Parse(File.ReadAllText(summaryPath))!;
            Assert.Empty(summary["not_executed"]!.AsArray());
            Assert.Equal("reused", Assert.Single(summary["steps"]!.AsArray())!["status"]!.ToString());
        }
    }

    [Theory]
    [InlineData("scribe")]
    [InlineData("current")]
    public void SelectedScribeAndPredicateRoutesUseTheirRegisteredUnits(string resource)
    {
        using var fixture = new ResourceFixture([resource]);
        fixture.Processes();
        var ids = resource == "scribe" ? new[] { "scribe-describe", "scribe-markdown", "scribe-projections" } : new[] { "SL-015" };
        fixture.CompleteCheckBoundary(ids);
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        Assert.Equal(new[] { "lean-report", resource == "scribe" ? "scribe" : "check-current" },
            CommonExecutionEvidence.ValidateCurrent(fixture.Root).Steps.Select(step => step.Name));
        Assert.Equal(ids, CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root, CommonExecutionEvidence.ChecksPath("current")).Units.Select(unit => unit.Id));
        Assert.Equal(new[] { "make --no-print-directory lean-report", "dotnet check-current" }, File.ReadAllLines(Path.Combine(fixture.Root, "build/launched")));
    }

    [Theory]
    [InlineData(false, "missing")]
    [InlineData(false, "invalid")]
    [InlineData(false, "materials")]
    [InlineData(true, "missing")]
    [InlineData(true, "invalid")]
    [InlineData(true, "materials")]
    public void FinalizationRejectsBadReportWithoutACandidateChecker(bool filemap, string damage)
    {
        using var fixture = new ResourceFixture(filemap ? ["lean-report", "filemap"] : ["lean-report"]);
        fixture.Processes();
        var report = Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath);
        if (damage == "missing") File.Delete(report);
        if (damage == "invalid") File.WriteAllText(report, "not JSON");
        if (damage == "materials") File.WriteAllText(report + ".materials.zip", "not a ZIP archive");

        using var output = new StringWriter();
        Assert.Equal(2, fixture.Run("current", output));
        var launched = File.ReadAllLines(Path.Combine(fixture.Root, "build/launched"));
        Assert.Equal(filemap ? new[] { "make --no-print-directory lean-report", "dotnet filemap-conform" }
            : ["make --no-print-directory lean-report"], launched);
        Assert.Contains("CURRENT_FINALIZE phase=seal status=started", output.ToString(), StringComparison.Ordinal);
        Assert.DoesNotContain("CURRENT_FINALIZE phase=seal status=completed", output.ToString(), StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath)));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void InspectorCompileObligationReachesTheReportEntryFromRegistration(bool compile)
    {
        using var fixture = new ResourceFixture([compile ? "lean-inspector-build" : "lean-report"]);
        fixture.Processes();
        fixture.Write("build/bin/make", "#!/bin/bash\nset -euo pipefail\nprintf '%s' \"${STRATALINT_LEAN_BUILD_TARGETS:-[]}\" > build/program-targets.json\n");
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        var targets = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/program-targets.json")))!.AsArray();
        Assert.Equal(compile ? new[] { "FixtureAudit", "fixture/inspector" } : [],
            targets.Select(value => value!.GetValue<string>()));
        Assert.Equal(new[] { "lean-report" }, CommonExecutionEvidence.ValidateCurrent(fixture.Root).Steps.Select(step => step.Name));
    }

    [Fact]
    public void DeltaCannotSubstituteAnotherBaseForTheValidatedPrScope()
    {
        using var fixture = new ResourceFixture(["filemap"]);
        fixture.PrPlan();
        using var output = new StringWriter();
        Assert.Equal(2, Program.Run(["delta", "--repository", fixture.Root, "--base", new string('a', 40),
            "--plan", fixture.Plan, "--changes", fixture.Changes], TestResultEvidence.Load, output, output));
        var result = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/ci/delta-result.json")))!;
        Assert.Equal("delta requires the validated plan's explicit immutable base", result["error"]!.ToString());
        Assert.DoesNotContain("STAGE_PROCESS ", output.ToString(), StringComparison.Ordinal);
        Assert.Equal("failed", result["status"]!.ToString());
    }

    [Fact]
    public void PrScopeIsTheExactImmutableBaseToMergeDifference()
    {
        using var fixture = new ResourceFixture(["filemap"]);
        fixture.PrPlan();
        fixture.Processes();
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        var selection = JsonNode.Parse(File.ReadAllText(fixture.Changes))!;
        Assert.Equal("pr", selection["mode"]!.ToString());
        selection["changes"] = new JsonArray();
        selection["change_count"] = 0;
        File.WriteAllText(fixture.Changes, selection.ToJsonString());
        output.GetStringBuilder().Clear();
        Assert.Equal(2, fixture.Run("current", output));
        Assert.Contains("incomplete or mismatched PR changed-path list", output.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void CompleteCurrentRouteSealsAllOriginalObligations()
    {
        using var fixture = new ResourceFixture(["lean-report"]);
        fixture.Processes(bindPlan: false);
        fixture.CompleteCheckBoundary();
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output, planned: false) == 0, output.ToString());
        var record = CommonExecutionEvidence.ValidateCurrent(fixture.Root);
        Assert.Null(record.Selection);
        Assert.Equal(new[] { "lean-report", "scribe", "filemap", "check-current" }, record.Steps.Select(step => step.Name));
        Assert.Equal(new[] { "make --no-print-directory lean-report", "dotnet check-current" }, File.ReadAllLines(Path.Combine(fixture.Root, "build/launched")));
        var checks = CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root, CommonExecutionEvidence.ChecksPath("current"));
        Assert.Equal(21, checks.Units.Length);
        Assert.Equal(CommonCheckRegistrationFixture.Ids
            .Where(id => id is not ("selftest-pair" or "capability-proof" or "banned-api-proof")).Order(StringComparer.Ordinal),
            checks.Units.Select(unit => unit.Id));
        Assert.All(checks.Units, unit => Assert.Equal("executed", unit.Status));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SelectedCurrentSeedRetainsProvenanceAndRerunsCorruptOrFailedUnit(bool failure)
    {
        using var fixture = new ResourceFixture(["filemap"]);
        fixture.Processes();
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        var original = Assert.Single(CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root, CommonExecutionEvidence.ChecksPath("current")).Units);
        var seed = Path.Combine(fixture.Root, CommonExecutionEvidence.CheckSeedPath("current"));
        File.AppendAllText(Path.Combine(seed, original.Operations.Single().Log), "corrupt optional input");
        if (failure) fixture.FilemapFailure();
        output.GetStringBuilder().Clear();
        var exit = fixture.Run("current", output);
        Assert.Equal(failure ? 1 : 0, exit);
        Assert.Equal(2, File.ReadAllLines(Path.Combine(fixture.Root, "build/launched")).Length);
        if (failure)
        {
            Assert.Contains("COMMON_CHECK_FAILED filemap", output.ToString(), StringComparison.Ordinal);
            Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath)));
        }
        else
        {
            var rerun = Assert.Single(CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root, CommonExecutionEvidence.ChecksPath("current")).Units);
            Assert.Equal("executed", rerun.Status);
            Assert.NotEqual(original.Operations.Single().Log, rerun.Operations.Single().Log);
            CommonExecutionEvidence.ValidateCurrent(fixture.Root);
        }
    }

    [Theory]
    [InlineData("lean")]
    [InlineData("lean-report")]
    [InlineData("filemap")]
    public void SelectedTransportRequiresExactlyItsDeclaredEvidence(string resource)
    {
        using var fixture = new ResourceFixture([resource]);
        fixture.Processes();
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        string[] Args(string action) => [action, "--repository", fixture.Root, "--stage", "current", "--commit", fixture.Commit, "--run-id", "17", "--run-attempt", "2"];
        Assert.True(Program.Run([.. Args("transport-pack"), "--archive", Path.Combine(fixture.Root, "build/current.tgz")], TestResultEvidence.Load, output, output) == 0, output.ToString());
        Assert.Equal(0, Program.Run(Args("transport-verify"), TestResultEvidence.Load, output, output));
        var transport = CommonExecutionEvidence.Read<CiTransportRecord>(fixture.Root, CiTransport.ManifestPath("current"));
        Assert.Equal(1, transport.Version);
        Assert.Equal(2, CommonExecutionEvidence.ValidateCurrent(fixture.Root).Version);
        Assert.Equal(resource == "lean-report", transport.Materials.Any(material => material.Path == CommonExecutionEvidence.ReportPath));
        var listPath = Path.Combine(fixture.Root, CommonExecutionEvidence.BundleListPath("current"));
        var list = File.ReadAllText(listPath);
        fixture.Write("build/unrequested.txt", "unrequested");
        File.WriteAllText(listPath, list + "build/unrequested.txt\0");
        Assert.Equal(2, Program.Run([.. Args("transport-pack"), "--archive", Path.Combine(fixture.Root, "build/extra.tgz")], TestResultEvidence.Load, output, output));
        File.WriteAllText(listPath, list);
        var record = CommonExecutionEvidence.Read<CommonStageRecord>(fixture.Root, CommonExecutionEvidence.CurrentPath);
        CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.CurrentPath, record with { Steps = [] });
        Assert.Equal(2, Program.Run(Args("transport-verify"), TestResultEvidence.Load, output, output));
    }

    [Fact]
    public void SelectedReportTransportAcceptsProducedDeclaredMaterial()
    {
        using var fixture = new ResourceFixture(["lean-report"]);
        var produced = NativeReportFixture.ProduceReport(fixture.Root);
        testOutput.WriteLine(produced.Text);
        Assert.True(produced.Exit == 0, produced.Text);
        fixture.CommitPlan();
        fixture.Processes(prepareReport: false);
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        Assert.Equal(0, Program.Run(["transport-pack", "--repository", fixture.Root, "--stage", "current",
            "--commit", fixture.Commit, "--run-id", "17", "--run-attempt", "2", "--archive", Path.Combine(fixture.Root, "build/current.tgz")],
            TestResultEvidence.Load, output, output));
        Assert.Equal(0, Program.Run(["transport-verify", "--repository", fixture.Root, "--stage", "current",
            "--commit", fixture.Commit, "--run-id", "17", "--run-attempt", "2"],
            TestResultEvidence.Load, output, output));
        Assert.Equal(new[] { "make --no-print-directory lean-report" }, File.ReadAllLines(Path.Combine(fixture.Root, "build/launched")));
    }

    [Fact]
    public void PlanWithoutExactScopeCannotExecute()
    {
        using var fixture = new ResourceFixture([]);
        using var output = new StringWriter();
        Assert.Equal(2, Program.Run(["current", "--repository", fixture.Root, "--plan", fixture.Plan], TestResultEvidence.Load, output, output));
        Assert.Contains("--plan requires the exact --changes scope input", output.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("scope")]
    [InlineData("filemap")]
    [InlineData("plan")]
    [InlineData("mode")]
    public void PlanScopeAndFilemapTamperingIsRejected(string defect)
    {
        using var fixture = new ResourceFixture(["filemap"]);
        fixture.Processes();
        if (defect == "filemap") File.AppendAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"), "# changed\n");
        else
        {
            var path = defect == "plan" ? fixture.Plan : fixture.Changes;
            var doc = JsonNode.Parse(File.ReadAllText(path))!;
            if (defect == "plan") doc["filemap_sha256"] = new string('a', 64);
            else if (defect == "mode") doc["mode"] = "pr";
            else { doc["changes"] = new JsonArray(); doc["change_count"] = 0; }
            File.WriteAllText(path, doc.ToJsonString());
        }
        using var output = new StringWriter();
        Assert.Equal(2, fixture.Run("current", output));
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/launched")));
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath)));
    }

    [Fact]
    public void RegisteredCheckInputsDoNotBecomeBuildRoots()
    {
        using var fixture = new ResourceFixture(["filemap"]);
        fixture.InputOnlyProjects();
        using var output = new StringWriter();
        Assert.True(fixture.Run("build", output) == 0, output.ToString());
        Assert.Equal(new[] { ResourceFixture.Foo }, CommonExecutionEvidence.ValidateBuild(fixture.Root).Projects);
        Assert.DoesNotContain("tools/ScriptTests/ScriptTests.csproj", output.ToString(), StringComparison.Ordinal);
        Assert.DoesNotContain("tools/Proof/Proof.csproj", output.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void SelectedBuildUsesUnionOfRegisteredRoots()
    {
        using var fixture = new ResourceFixture(["filemap", "lean"]);

        using var output = new StringWriter();
        Assert.True(fixture.Run("build", output) == 0, output.ToString());
        var processes = output.ToString().Split('\n').Where(line => line.StartsWith("STAGE_PROCESS ", StringComparison.Ordinal))
            .Select(line => JsonNode.Parse(line["STAGE_PROCESS ".Length..])!).ToArray();
        Assert.Equal(new[] { "restore", "build" }, processes.Select(row => row["arguments"]![0]!.ToString()));
        var projectSet = processes[0]["arguments"]![1]!.ToString();
        Assert.Equal(projectSet, processes[1]["arguments"]![1]!.ToString());
        var expectedRoots = new[] { ResourceFixture.Foo, ResourceFixture.Bar }.Order(StringComparer.Ordinal).ToArray();
        Assert.Equal(expectedRoots, XDocument.Load(projectSet).Root!.Elements("Project")
            .Select(project => Path.GetRelativePath(fixture.Root, project.Attribute("Path")!.Value).Replace('\\', '/')).Order(StringComparer.Ordinal));
        Assert.All(processes, row => Assert.Contains(row["arguments"]!.AsArray(), arg => arg!.ToString() == "-nr:false"));
        var build = CommonExecutionEvidence.ValidateBuild(fixture.Root);
        Assert.Equal(expectedRoots, build.Projects);
        Assert.Contains(build.Materials, material => material.Path.EndsWith("/Foo.dll", StringComparison.Ordinal));
        Assert.Contains(build.Materials, material => material.Path.EndsWith("/Bar.dll", StringComparison.Ordinal));
        Assert.DoesNotContain(build.Materials, material => material.Path.StartsWith(CommonBuildOutputs.PackagesPath + "/", StringComparison.Ordinal));
        File.Copy(fixture.Plan, Path.Combine(fixture.Root, "build/alternate-plan.json"));
        CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.BuildPath,
            build with { Selection = build.Selection! with { Plan = "build/alternate-plan.json" } });
        Assert.Contains("missing resource selection materials", Assert.Throws<InvalidDataException>(() =>
            CommonExecutionEvidence.ValidateBuild(fixture.Root)).Message, StringComparison.Ordinal);
    }

}
