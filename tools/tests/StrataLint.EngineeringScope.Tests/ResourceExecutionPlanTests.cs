using System.Text.Json.Nodes;
using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class ResourceExecutionPlanTests
{
    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void PlannedEngineeringRunsAndAcceptsOnlySelectedProjects(bool compiledTestDependency, bool selectDependency)
    {
        using var fixture = new SelectedTestsFixture(compiledTestDependency, selectDependency: selectDependency);
        var calls = new List<string>();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Tree.Root, (project, directory) =>
        {
            calls.Add(project);
            fixture.Tree.WriteTrx(directory, "Passed");
            return 0;
        }, TextWriter.Null));
        Assert.Equal(selectDependency ? new[] { CurrentExecutionContractTests.CandidateFixture.First, CurrentExecutionContractTests.CandidateFixture.Second }
            : [CurrentExecutionContractTests.CandidateFixture.First], calls);
        var tests = CommonExecutionEvidence.ValidateTests(fixture.Tree.Root,
            [CurrentExecutionContractTests.CandidateFixture.First, CurrentExecutionContractTests.CandidateFixture.Second]);
        Assert.Equal(calls, tests.Projects.Select(project => project.Project));
        Assert.All(tests.Projects, project => Assert.Equal("executed", project.Status));
    }

    [Fact]
    public void PlannedEngineeringSealsOnlySelectedChecks()
    {
        using var fixture = new SelectedTestsFixture();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Tree.Root, (_, directory) =>
        {
            fixture.Tree.WriteTrx(directory, "Passed");
            return 0;
        }, TextWriter.Null));
        var build = CommonExecutionEvidence.ValidateBuild(fixture.Tree.Root);
        CheckEvidenceFixture.Seal(fixture.Tree.Root, "engineering", build, ["selftest-pair"]);
        fixture.Tree.Write("build/tests.log", "selected project succeeded\n");
        CommonExecutionEvidence.SealEngineering(fixture.Tree.Root, build,
            [new StageStep("tests", 0, 0, "executed", "build/tests.log")]);
        CommonExecutionEvidence.ValidateEngineering(fixture.Tree.Root, out var tests, out var checks);
        Assert.NotNull(tests);
        Assert.Single(tests.Projects);
        Assert.Equal(new[] { "selftest-pair" }, checks.Units.Select(unit => unit.Id));
    }

    [Theory]
    [InlineData("intact")]
    [InlineData("invalid-row")]
    [InlineData("corrupt-trx")]
    public void SelectedTestSeedKeepsSuccessfulUnselectedProjectsForLaterRounds(string damage)
    {
        using var fixture = new SelectedTestsFixture(priorSeed: true);
        var seedPath = Path.Combine(fixture.Tree.Root, CommonExecutionEvidence.TestSeedPath, "tests.json");
        var previous = JsonNode.Parse(File.ReadAllText(seedPath))!;
        if (damage == "invalid-row")
        {
            previous["projects"]!.AsArray().Add(42);
            File.WriteAllText(seedPath, previous.ToJsonString());
        }
        if (damage == "corrupt-trx")
        {
            var second = previous["projects"]!.AsArray().Single(row => row!["project"]!.ToString() == CurrentExecutionContractTests.CandidateFixture.Second)!;
            File.AppendAllText(Path.Combine(fixture.Tree.Root, CommonExecutionEvidence.TestSeedPath, second["results"]!.ToString(), "execution.trx"), "corrupt");
        }
        Assert.Equal(0, Program.RunCurrentTests(fixture.Tree.Root, (_, _) =>
            throw new InvalidOperationException("selected unchanged project must reuse its seed"), TextWriter.Null));
        var build = CommonExecutionEvidence.ValidateBuild(fixture.Tree.Root);
        CheckEvidenceFixture.Seal(fixture.Tree.Root, "engineering", build, ["selftest-pair"]);
        fixture.Tree.Write("build/tests.log", "selected project reused\n");
        CommonExecutionEvidence.SealEngineering(fixture.Tree.Root, build, [new StageStep("tests", 0, 0, "executed", "build/tests.log")]);
        Assert.True(CommonExecutionEvidence.ExportTestSeed(fixture.Tree.Root, TextWriter.Null));
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Tree.Root, "engineering", TextWriter.Null));
        var seed = CommonExecutionEvidence.Read<TestExecutionRecord>(fixture.Tree.Root, CommonExecutionEvidence.TestSeedPath + "/tests.json");
        var transported = File.ReadAllText(Path.Combine(fixture.Tree.Root, CommonExecutionEvidence.BundleListPath("engineering-seed"))).Split('\0');
        Assert.All(seed.Materials, material => Assert.Contains(CommonExecutionEvidence.TestSeedPath + "/" + material.Path, transported));
        Assert.Equal(damage == "corrupt-trx" ? [CurrentExecutionContractTests.CandidateFixture.First]
            : new[] { CurrentExecutionContractTests.CandidateFixture.First, CurrentExecutionContractTests.CandidateFixture.Second },
            seed.Projects.Select(project => project.Project));
        fixture.Tree.Build();
        var calls = new List<string>();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Tree.Root, (project, directory) =>
        {
            calls.Add(project);
            fixture.Tree.WriteTrx(directory, "Passed");
            return 0;
        }, TextWriter.Null));
        Assert.Equal(damage == "corrupt-trx" ? new[] { CurrentExecutionContractTests.CandidateFixture.Second } : [], calls);
        CommonExecutionEvidence.ValidateTests(fixture.Tree.Root);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void GuardOnlyEngineeringDoesNotInventTestExecutionEvidence(bool priorSeed)
    {
        using var fixture = new SelectedTestsFixture(priorSeed: priorSeed, testsRequired: false);
        var root = fixture.Tree.Root;
        File.Delete(Path.Combine(root, CommonExecutionEvidence.TestsPath));
        var build = CommonExecutionEvidence.ValidateBuild(root);
        CheckEvidenceFixture.Seal(root, "engineering", build, ["selftest-pair"]);
        CommonExecutionEvidence.SealEngineering(root, build, []);
        var engineering = CommonExecutionEvidence.ValidateEngineering(root, out var tests, out var checks);
        Assert.Null(tests);
        Assert.Empty(engineering.Steps);
        Assert.Single(checks.Units);
        Assert.DoesNotContain(engineering.Materials, material => material.Path == CommonExecutionEvidence.TestsPath);
        Assert.False(CommonExecutionEvidence.ExportTestSeed(root, TextWriter.Null));
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(root, "engineering", TextWriter.Null));
        if (priorSeed)
        {
            var seed = CommonExecutionEvidence.Read<TestExecutionRecord>(root, CommonExecutionEvidence.TestSeedPath + "/tests.json");
            Assert.Equal(2, seed.Projects.Length);
            var transported = File.ReadAllText(Path.Combine(root, CommonExecutionEvidence.BundleListPath("engineering-seed"))).Split('\0');
            Assert.All(seed.Materials, material => Assert.Contains(CommonExecutionEvidence.TestSeedPath + "/" + material.Path, transported));
        }
    }

    [Theory]
    [InlineData("invalid-json")]
    [InlineData("invalid-row")]
    public void GuardOnlySeedTransportIgnoresDamagedOptionalTests(string damage)
    {
        using var fixture = new SelectedTestsFixture(priorSeed: true, testsRequired: false);
        var root = fixture.Tree.Root;
        var path = Path.Combine(root, CommonExecutionEvidence.TestSeedPath, "tests.json");
        if (damage == "invalid-json") File.WriteAllText(path, "not JSON");
        else
        {
            var seed = JsonNode.Parse(File.ReadAllText(path))!;
            seed["projects"]!.AsArray().Add(42);
            File.WriteAllText(path, seed.ToJsonString());
        }
        var build = CommonExecutionEvidence.ValidateBuild(root);
        CheckEvidenceFixture.Seal(root, "engineering", build, ["selftest-pair"]);
        CommonExecutionEvidence.SealEngineering(root, build, []);
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(root, "engineering", TextWriter.Null));
        CommonExecutionEvidence.ValidateEngineering(root, out var tests, out _);
        Assert.Null(tests);
        var retained = CommonExecutionEvidence.Read<TestExecutionRecord>(root, CommonExecutionEvidence.TestSeedPath + "/tests.json");
        Assert.Equal(damage == "invalid-json" ? 0 : 2, retained.Projects.Length);
    }

    [Fact]
    public void GuardOnlyStageLaunchesSelectedGuardAndNoTestRunner()
    {
        using var fixture = new SelectedTestsFixture(testsRequired: false);
        var root = fixture.Tree.Root;
        fixture.Tree.Write("build/bin/dotnet", "#!/bin/bash\nset -euo pipefail\n[[ \"$*\" == *' selftest' ]]\nprintf 'SELFTEST PASS\\n'\nprintf 'selftest\\n' >> build/launched\n");
        if (!OperatingSystem.IsWindows())
            File.SetUnixFileMode(Path.Combine(root, "build/bin/dotnet"), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var build = CommonExecutionEvidence.ValidateBuild(root);
        var executable = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
        var result = SharedBuildContractTests.Process(root, executable,
            ["engineering", "--repository", root, "--build-round", build.Round,
                "--plan", "build/plan.json", "--changes", "build/changes.json"],
            new Dictionary<string, string> { ["PATH"] = Path.Combine(root, "build/bin") + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH") });
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal(new[] { "selftest", "selftest" }, File.ReadAllLines(Path.Combine(root, "build/launched")));
        CommonExecutionEvidence.ValidateEngineering(root, out var tests, out var checks);
        Assert.Null(tests);
        Assert.Equal("executed", Assert.Single(checks.Units).Status);
        var summary = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "build/ci/engineering-result.json")))!;
        Assert.Equal(new[] { "tests", "capability-proof", "banned-api-proof" },
            summary["not_required"]!.AsArray().Select(value => value!.ToString()));
        Assert.Empty(summary["not_executed"]!.AsArray());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EngineeringRejectsBuildBoundToDifferentScopeBeforeLaunchingWork(bool matched)
    {
        using var fixture = new SelectedTestsFixture(testsRequired: false);
        var root = fixture.Tree.Root;
        var build = CommonExecutionEvidence.ValidateBuild(root);
        var commit = SharedBuildContractTests.Process(root, "git", ["rev-parse", "HEAD"]).Text.Trim();
        var baseline = SharedBuildContractTests.Process(root, "git", ["rev-parse", "HEAD^1"]).Text.Trim();
        var scope = SharedBuildContractTests.Process(root, "python3", ["-B", "tools/scripts/workflow/ci.py", "push-plan",
            "--repository", root, "--commit", commit, "--before", baseline, "--after", commit]);
        Assert.True(scope.Exit == 0, scope.Text);
        var planned = SharedBuildContractTests.Process(root, "python3", ["-B", "tools/scripts/workflow/ci.py", "plan",
            "--repository", root, "--commit", commit, "--changes", "build/ci/changes.json", "--output", "build/other-plan.json"]);
        Assert.True(planned.Exit == 0, planned.Text);
        fixture.Tree.Write("build/bin/dotnet", "#!/bin/bash\nset -euo pipefail\n[[ \"$*\" == *' selftest' ]]\nprintf 'SELFTEST PASS\\n'\nprintf 'selftest\\n' >> build/launched\n");
        if (!OperatingSystem.IsWindows())
            File.SetUnixFileMode(Path.Combine(root, "build/bin/dotnet"), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var executable = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
        var result = SharedBuildContractTests.Process(root, executable,
            ["engineering", "--repository", root, "--build-round", build.Round,
                "--plan", matched ? "build/plan.json" : "build/other-plan.json",
                "--changes", matched ? "build/changes.json" : "build/ci/changes.json"],
            new Dictionary<string, string> { ["PATH"] = Path.Combine(root, "build/bin") + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH") });
        Assert.Equal(matched ? 0 : 2, result.Exit);
        if (matched) Assert.Equal(2, File.ReadAllLines(Path.Combine(root, "build/launched")).Length);
        else
        {
            Assert.Contains("engineering requires the same resource plan as build", result.Text, StringComparison.Ordinal);
            Assert.False(File.Exists(Path.Combine(root, "build/launched")));
            Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.EngineeringPath)));
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DeclaredCurrentOnlyRoundDoesNotRequireEngineeringEvidence(bool pr)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["lean-report"]);
        if (pr) fixture.PrPlan();
        fixture.Processes();
        var build = CommonExecutionEvidence.ValidateBuild(fixture.Root);
        var plan = ResourceExecutionPlan.Load(fixture.Root, fixture.Plan, fixture.Changes)!;
        CommonExecutionEvidence.SealBuild(fixture.Root, build.Candidate, build.Materials.Select(material => material.Path),
            build.Steps, plan.Projects, plan.Retain(fixture.Root));
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        var common = CommonExecutionEvidence.ValidateCommon(fixture.Root);
        Assert.Null(common.Engineering);
        Assert.Null(common.Tests);
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.EngineeringPath)));
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateCommon(fixture.Root,
            [CurrentExecutionContractTests.CandidateFixture.First]));
        if (pr)
            Assert.Null(CommonExecutionEvidence.ValidateCommon(fixture.Root,
                protectedBase: plan.Document.GetProperty("base").GetString()).Engineering);
        else
            Assert.Contains("delta requires a matching PR resource plan", Assert.Throws<InvalidDataException>(() =>
                CommonExecutionEvidence.ValidateCommon(fixture.Root, protectedBase: fixture.Commit)).Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("push")]
    [InlineData("current")]
    [InlineData("pr")]
    public void DeltaRejectsCommonBuildFromAnotherScopeMode(string mode)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["lean-report"]);
        var mapping = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "Meta/ci-resources.json")))!;
        mapping["resources"]!.AsArray().Add(JsonNode.Parse("""{"id":"delta","projects":[],"checks":[],"steps":[]}"""));
        fixture.Write("Meta/ci-resources.json", mapping.ToJsonString());
        fixture.Write("Meta/FILEMAP.toml", File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"))
            .Replace("  { id = \"filemap\"", "  { id = \"delta\", stage = \"delta\", owner = \"tools/scripts/workflow/ci.py\", prerequisites = [\"lean-report\"], tools = [], cache_layers = [], cache_activation = {}, materials = [] },\n"
                + "  { id = \"filemap\"", StringComparison.Ordinal)
            .Replace("require = [\"lean-report\"]", "require = [\"delta\",\"lean-report\"]", StringComparison.Ordinal));
        fixture.CommitPlan();
        fixture.PrPlan();
        var prPlan = Path.Combine(fixture.Root, "build/pr-plan.json");
        var prChanges = Path.Combine(fixture.Root, "build/pr-changes.json");
        File.Copy(fixture.Plan, prPlan);
        File.Copy(fixture.Changes, prChanges);
        Assert.Equal("required", JsonNode.Parse(File.ReadAllText(prPlan))!["stages"]!["delta"]!["status"]!.ToString());
        var baseline = JsonNode.Parse(File.ReadAllText(prChanges))!["base"]!.ToString();
        if (mode == "push")
        {
            var scope = SharedBuildContractTests.Process(fixture.Root, "python3", ["-B", "tools/scripts/workflow/ci.py", "push-plan",
                "--repository", fixture.Root, "--commit", fixture.Commit, "--before", baseline, "--after", fixture.Commit]);
            Assert.True(scope.Exit == 0, scope.Text);
            File.Copy(Path.Combine(fixture.Root, "build/ci/changes.json"), fixture.Changes, overwrite: true);
        }
        else if (mode == "current")
        {
            var scope = JsonNode.Parse(File.ReadAllText(fixture.Changes))!;
            scope["mode"] = "current";
            scope["base"] = null;
            scope["head"] = null;
            File.WriteAllText(fixture.Changes, scope.ToJsonString());
        }
        var planned = SharedBuildContractTests.Process(fixture.Root, "python3", ["-B", "tools/scripts/workflow/ci.py", "plan",
            "--repository", fixture.Root, "--commit", fixture.Commit, "--changes", fixture.Changes, "--output", fixture.Plan]);
        Assert.True(planned.Exit == 0, planned.Text);
        fixture.Processes();
        var build = CommonExecutionEvidence.ValidateBuild(fixture.Root);
        var selection = ResourceExecutionPlan.Load(fixture.Root, fixture.Plan, fixture.Changes)!;
        CommonExecutionEvidence.SealBuild(fixture.Root, build.Candidate, build.Materials.Select(material => material.Path),
            build.Steps, selection.Projects, selection.Retain(fixture.Root));
        fixture.Write("build/bin/dotnet", "#!/bin/bash\nexit 0\n");
        var executable = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
        var result = SharedBuildContractTests.Process(fixture.Root, executable, ["delta", "--repository", fixture.Root,
                "--base", baseline, "--plan", prPlan, "--changes", prChanges],
            new Dictionary<string, string> { ["PATH"] = Path.Combine(fixture.Root, "build/bin") + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH") });
        Assert.Equal(mode == "pr" ? 0 : 2, result.Exit);
        if (mode == "pr") Assert.Contains("\"command\":\"dotnet\"", result.Text, StringComparison.Ordinal);
        else
        {
            Assert.Contains("delta requires a matching PR resource plan", result.Text, StringComparison.Ordinal);
            Assert.DoesNotContain("\"command\":\"dotnet\"", result.Text, StringComparison.Ordinal);
        }
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("failed")]
    public void SelectedProjectCannotPassWithoutSuccessfulTrx(string evidence)
    {
        using var fixture = new SelectedTestsFixture();
        var calls = 0;
        var exit = Program.RunCurrentTests(fixture.Tree.Root, (_, directory) =>
        {
            ++calls;
            if (evidence == "failed") fixture.Tree.WriteTrx(directory, "Failed");
            return 0;
        }, TextWriter.Null);
        Assert.Equal(1, calls);
        Assert.Equal(1, exit);
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateTests(fixture.Tree.Root));
    }

    private sealed class SelectedTestsFixture : IDisposable
    {
        internal CurrentExecutionContractTests.CandidateFixture Tree { get; } = new();

        internal SelectedTestsFixture(bool compiledTestDependency = false, bool priorSeed = false, bool testsRequired = true, bool selectDependency = false)
        {
            if (priorSeed)
            {
                Assert.Equal(0, Program.RunCurrentTests(Tree.Root, (_, directory) =>
                {
                    Tree.WriteTrx(directory, "Passed");
                    return 0;
                }, TextWriter.Null));
                var initial = CommonExecutionEvidence.ValidateBuild(Tree.Root);
                CheckEvidenceFixture.Seal(Tree.Root, "engineering", initial);
                Tree.Write("build/tests.log", "initial successful projects\n");
                CommonExecutionEvidence.SealEngineering(Tree.Root, initial, [new StageStep("tests", 0, 0, "executed", "build/tests.log")]);
                Assert.True(CommonExecutionEvidence.ExportTestSeed(Tree.Root, TextWriter.Null));
            }
            if (compiledTestDependency)
            {
                var manifest = JsonNode.Parse(File.ReadAllText(Path.Combine(Tree.Root, EngineeringRegistrationFixture.Path)))!;
                manifest["projects"]!.AsArray().Single(row => row!["path"]!.ToString() == CurrentExecutionContractTests.CandidateFixture.First)!["references"]
                    = new JsonArray(CurrentExecutionContractTests.CandidateFixture.Second);
                Tree.Write(EngineeringRegistrationFixture.Path, manifest.ToJsonString());
            }
            const string judge = "tools/Judge/Judge.csproj";
            if (!testsRequired)
            {
                Tree.Write(judge, "<Project />\n");
                Tree.Write("tools/Judge/Program.cs", "// fixture producer\n");
                Tree.Write(EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Append(
                    File.ReadAllText(Path.Combine(Tree.Root, EngineeringRegistrationFixture.Path)),
                    new EngineeringProjectFixture(judge, "Judge", "test-support", false, ["tools/Judge/Program.cs"])));
            }
            var source = TestRepositoryLayout.FindRoot();
            foreach (var path in new[] { "tools/scripts/workflow/ci.py", "tools/scripts/workflow/ci_plan.py" })
                Tree.Write(path, File.ReadAllText(Path.Combine(source, path)));
            Tree.Write("Meta/ci-resources.json", JsonSerializer.Serialize(new { schema = "ci-resource-execution-v1", resources = new[] {
                new { id = "build", projects = Array.Empty<string>(), checks = Array.Empty<string>(), steps = Array.Empty<string>() },
                new { id = "test-selected", projects = selectDependency
                        ? new[] { CurrentExecutionContractTests.CandidateFixture.First, CurrentExecutionContractTests.CandidateFixture.Second }
                        : new[] { testsRequired ? CurrentExecutionContractTests.CandidateFixture.First : judge },
                    checks = new[] { "selftest-pair" }, steps = Array.Empty<string>() } } }));
            Tree.Write("Meta/FILEMAP.toml", """
                schema_version = 4
                resources = [
                  { id = "build", stage = "build", owner = "tools/scripts/workflow/ci.py", prerequisites = [], tools = [], cache_layers = [], cache_activation = {}, materials = ["Meta/ci-checks.json", "Meta/ci-resources.json", "Meta/engineering-projects.json"] },
                  { id = "test-selected", stage = "engineering", owner = "tools/scripts/workflow/ci.py", prerequisites = ["build"], tools = [], cache_layers = [], cache_activation = {}, materials = [] },
                ]
                [residence_policy]
                case_id = "FIXTURE"
                desired = "registered"
                known_violation_count = 0
                status = "closed"
                [[files]]
                pattern = "**"
                require = ["test-selected"]
                kind = "program"
                admission_plane = "judge"
                produced_by = "none"
                consumed_by = ["test"]
                verified_by = ["test"]
                artifact_id = "none"
                runtime_disposition = "committed-source"
                """ + "\n");
            Run("git", ["add", "."]);
            Run("git", ["-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "selected tests"]);
            var commit = Run("git", ["rev-parse", "HEAD"]);
            var entry = Run("git", ["ls-tree", "HEAD", "--", "Meta/ci-resources.json"]).Split([' ', '\t'], StringSplitOptions.RemoveEmptyEntries);
            Tree.Write("build/changes.json", JsonSerializer.Serialize(new { schema_version = 1, mode = "current",
                candidate = new { commit, tree = Run("git", ["rev-parse", "HEAD^{tree}"]) }, @base = (string?)null, head = (string?)null,
                complete = true, change_count = 1, changes = new[] { new { status = "A", old = (object?)null,
                    @new = new { path = "Meta/ci-resources.json", mode = entry[0], oid = entry[2] } } } }));
            Run("python3", ["-B", "tools/scripts/workflow/ci.py", "plan", "--repository", Tree.Root,
                "--commit", commit, "--changes", "build/changes.json", "--output", "build/plan.json"]);
            var plan = ResourceExecutionPlan.Load(Tree.Root, "build/plan.json", "build/changes.json")!;
            var build = Tree.Build();
            var tests = CommonExecutionEvidence.Read<BuiltTestProject[]>(Tree.Root, CommonBuildOutputs.TestsPath)
                .Where(project => plan.TestProjects.Contains(project.Project)).ToArray();
            CommonExecutionEvidence.Write(Tree.Root, CommonBuildOutputs.TestsPath, tests);
            var selection = plan.Retain(Tree.Root);
            CommonExecutionEvidence.SealBuild(Tree.Root, build.Candidate,
                build.Materials.Select(material => material.Path).Concat([selection.Plan, selection.Changes]),
                build.Steps, plan.Projects, selection);
        }

        private string Run(string command, string[] arguments)
        {
            var result = SharedBuildContractTests.Process(Tree.Root, command, arguments);
            Assert.True(result.Exit == 0, result.Text);
            return result.Text.Trim();
        }

        public void Dispose() => Tree.Dispose();
    }

    [Fact]
    public void ForgedCandidateIsRejectedBeforeStageExecution()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        var plan = JsonNode.Parse(File.ReadAllText(fixture.Plan))!;
        plan["candidate"]!["commit"] = new string('a', 40);
        File.WriteAllText(fixture.Plan, plan.ToJsonString());
        Assert.Throws<InvalidDataException>(() => ResourceExecutionPlan.Load(fixture.Root, fixture.Plan, fixture.Changes));
    }

    [Fact]
    public void ResourceSubsetMustContainRegisteredPrerequisites()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        var plan = JsonNode.Parse(File.ReadAllText(fixture.Plan))!;
        plan["resources"] = new JsonArray("filemap");
        plan["stages"]!["build"]!["resources"] = new JsonArray();
        plan["stages"]!["build"]!["status"] = "not-required";
        File.WriteAllText(fixture.Plan, plan.ToJsonString());
        Assert.Throws<InvalidDataException>(() => ResourceExecutionPlan.Load(fixture.Root, fixture.Plan, fixture.Changes));
    }
}
