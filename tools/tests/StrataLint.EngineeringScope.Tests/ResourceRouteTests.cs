using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class ResourceRouteTests
{
    [Fact]
    public void NoResourceStageRetainsGitIdentityAndClearsAcceptance()
    {
        using var fixture = new ResourceFixture([]);
        fixture.Write(CommonExecutionEvidence.CurrentPath, "stale");
        fixture.Write(CommonExecutionEvidence.ChecksPath("current"), "stale");
        fixture.Write(CommonExecutionEvidence.CheckSeedPath("current") + "/keep", "optional");
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        var result = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/ci/current-result.json")))!;
        Assert.Equal(fixture.Commit, result["git_candidate"]!["commit"]!.ToString());
        Assert.Equal("not-required", result["status"]!.ToString());
        Assert.Empty(result["steps"]!.AsArray());
        Assert.Empty(result["artifacts"]!.AsArray());
        Assert.DoesNotContain("STAGE_PROCESS ", output.ToString(), StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath)));
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.ChecksPath("current"))));
        Assert.Equal("optional", File.ReadAllText(Path.Combine(fixture.Root, CommonExecutionEvidence.CheckSeedPath("current"), "keep")));
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
        fixture.Processes();
        fixture.CompleteCheckBoundary();
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output, planned: false) == 0, output.ToString());
        var record = CommonExecutionEvidence.ValidateCurrent(fixture.Root);
        Assert.Null(record.Selection);
        Assert.Equal(new[] { "lean-report", "scribe", "filemap", "check-current" }, record.Steps.Select(step => step.Name));
        Assert.Equal(new[] { "make --no-print-directory lean-report", "dotnet check-current" }, File.ReadAllLines(Path.Combine(fixture.Root, "build/launched")));
        Assert.Equal(22, CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root, CommonExecutionEvidence.ChecksPath("current")).Units.Length);
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
        Assert.Equal(failure ? 2 : 0, exit);
        Assert.Equal(2, File.ReadAllLines(Path.Combine(fixture.Root, "build/launched")).Length);
        if (failure) Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath)));
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
    public void SelectedReportSnapshotAcceptsProducedDeclaredMaterial()
    {
        using var fixture = new ResourceFixture(["lean-report"]);
        var produced = CiTransportTests.ProduceReport(fixture.Root);
        Assert.True(produced.Exit == 0, produced.Text);
        fixture.CommitPlan();
        fixture.Processes(prepareReport: false);
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        Assert.Equal(0, Program.Run(["transport-pack", "--repository", fixture.Root, "--stage", "current",
            "--commit", fixture.Commit, "--run-id", "17", "--run-attempt", "2", "--archive", Path.Combine(fixture.Root, "build/current.tgz")],
            TestResultEvidence.Load, output, output));
        var snapshot = SharedBuildContractTests.Process(fixture.Root, "python3", ["-B", "-c", """
            import json, pathlib, sys
            sys.path.insert(0, str(pathlib.Path(sys.argv[1]) / 'tools/scripts/worktree'))
            from lean_actions import snapshot_report
            root = pathlib.Path(sys.argv[2])
            seed = json.loads((root / '.lake/build/stratalint/raw-lean-report.json.seed.json').read_text())
            files = snapshot_report(root, seed['partition'], root / 'build/selected-report-snapshot')
            assert len(files) == 6, files
            """, TestRepositoryLayout.FindRoot(), fixture.Root], new Dictionary<string, string> {
                ["CANDIDATE_SHA"] = fixture.Commit, ["GITHUB_RUN_ID"] = "17", ["GITHUB_RUN_ATTEMPT"] = "2",
                ["GITHUB_REPOSITORY"] = Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "" });
        Assert.True(snapshot.Exit == 0, snapshot.Text);
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
        foreach (var verb in new[] { "restore", "build" })
            Assert.Equal(new[] { ResourceFixture.Foo, ResourceFixture.Bar }.Order(StringComparer.Ordinal),
                processes.Where(row => row["arguments"]![0]!.ToString() == verb).Select(row => row["arguments"]![1]!.ToString()).Order(StringComparer.Ordinal));
        Assert.All(processes, row => Assert.Contains(row["arguments"]!.AsArray(), arg => arg!.ToString() == "-nr:false"));
        Assert.DoesNotContain(".sln", output.ToString(), StringComparison.Ordinal);
        var build = CommonExecutionEvidence.ValidateBuild(fixture.Root);
        Assert.Contains(build.Materials, material => material.Path.EndsWith("/Foo.dll", StringComparison.Ordinal));
        Assert.Contains(build.Materials, material => material.Path.EndsWith("/Bar.dll", StringComparison.Ordinal));
        Assert.DoesNotContain(build.Materials, material => material.Path.StartsWith(CommonBuildOutputs.PackagesPath + "/", StringComparison.Ordinal));
        File.Copy(fixture.Plan, Path.Combine(fixture.Root, "build/alternate-plan.json"));
        CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.BuildPath,
            build with { Selection = build.Selection! with { Plan = "build/alternate-plan.json" } });
        Assert.Contains("missing resource selection materials", Assert.Throws<InvalidDataException>(() =>
            CommonExecutionEvidence.ValidateBuild(fixture.Root)).Message, StringComparison.Ordinal);
    }

    internal sealed class ResourceFixture : IDisposable
    {
        internal const string Foo = "tools/Foo/Foo.csproj";
        internal const string Bar = "tools/Bar/Bar.csproj";
        private readonly CurrentExecutionContractTests.CandidateFixture fixture = new();
        private string? processPath = Environment.GetEnvironmentVariable("PATH");
        private readonly string? physicalRoot;
        internal string Root => physicalRoot ?? fixture.Root;
        internal string Plan => Path.Combine(Root, "build/plan.json");
        internal string Changes => Path.Combine(Root, "build/changes.json");
        internal string Commit { get; private set; } = "";
        private readonly string changed;
        private readonly string[] required;
        internal ResourceFixture(string[] required, string changed = "fixtures/selected.txt")
        {
            this.required = required;
            this.changed = changed;
            physicalRoot = Git("rev-parse", "--show-toplevel");
            var source = TestRepositoryLayout.FindRoot();
            foreach (var path in new[] { "tools/scripts/workflow/ci.py", "tools/scripts/workflow/ci_plan.py", "tools/scripts/ci-build-outputs.targets" })
                Write(path, File.ReadAllText(Path.Combine(source, path)));
            Write(changed, "registered input\n");
            Write(".gitignore", "build/\n.lake/\n**/bin/\n**/obj/\n__pycache__/\n");
            foreach (var path in new[] { CurrentExecutionContractTests.CandidateFixture.First, CurrentExecutionContractTests.CandidateFixture.Second,
                "tools/tests/CompileFailProof/CompileFailProof.csproj", "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj",
                "tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs" })
                File.Delete(Path.Combine(Root, path));
            Write(PackageMaterialRegistry.RelativePath, JsonSerializer.Serialize(new {
                schemaVersion = 1, packageRootSource = "build-output:NuGetPackageRoot",
                packages = new[] { new { packagePath = "xunit/2.9.3", include = new[] { "xunit.nuspec" }, exclude = Array.Empty<string>() } } }));
            Register();
            CommitPlan();
        }
        private void Register()
        {
            var mapping = new[] {
                new { id = "build", projects = Array.Empty<string>(), checks = Array.Empty<string>(), steps = Array.Empty<string>() },
                new { id = "filemap", projects = new[] { Foo }, checks = new[] { "filemap" }, steps = new[] { "filemap" } },
                new { id = "lean", projects = new[] { Bar }, checks = Array.Empty<string>(), steps = new[] { "lean" } },
                new { id = "lean-report", projects = new[] { Bar }, checks = Array.Empty<string>(), steps = new[] { "lean-report" } },
                new { id = "scribe", projects = new[] { Foo }, checks = new[] { "scribe-describe", "scribe-markdown", "scribe-projections" }, steps = new[] { "scribe" } },
                new { id = "current", projects = new[] { Foo }, checks = new[] { "SL-015" }, steps = new[] { "check-current" } }
            };
            Write("Meta/ci-resources.json", JsonSerializer.Serialize(new { schema = "ci-resource-execution-v1", resources = mapping }));
            var rows = mapping.OrderBy(row => row.id, StringComparer.Ordinal).Select(row =>
                "  { id = \"" + row.id + "\", stage = \"" + (row.id == "build" ? "build" : "current")
                + "\", owner = \"tools/scripts/workflow/ci.py\", prerequisites = " + (row.id == "build" ? "[]" : row.id == "lean-report" ? "[\"lean\"]" : row.id is "scribe" or "current" ? "[\"lean-report\"]" : "[\"build\"]")
                + ", tools = [], cache_layers = [], materials = [\"Meta/ci-checks.json\", \"Meta/ci-resources.json\", \"Meta/engineering-projects.json\"] },");
            Write("Meta/FILEMAP.toml", "schema_version = 3\nresources = [\n" + string.Join("\n", rows) + "\n]\n"
                + "[residence_policy]\ncase_id = \"FIXTURE\"\ndesired = \"registered\"\nknown_violation_count = 0\nstatus = \"closed\"\n"
                + "[[files]]\npattern = \"**\"\nrequire = " + JsonSerializer.Serialize(required.Order(StringComparer.Ordinal)) + "\n"
                + "kind = \"program\"\nadmission_plane = \"judge\"\nproduced_by = \"none\"\nconsumed_by = [\"test\"]\nverified_by = [\"test\"]\nartifact_id = \"none\"\nruntime_disposition = \"committed-source\"\n");
            foreach (var (project, assembly) in new[] { (Foo, "Foo"), (Bar, "Bar") })
            {
                Write(project, "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><TargetFramework>net10.0</TargetFramework><OutputType>Exe</OutputType></PropertyGroup></Project>\n");
                Write(Path.GetDirectoryName(project)!.Replace('\\', '/') + "/Program.cs", "System.Console.WriteLine(\"fixture\");\n");
            }
            Write(EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(
                new EngineeringProjectFixture(Foo, "Foo", "test-support", false, ["tools/Foo/Program.cs"]),
                new EngineeringProjectFixture(Bar, "Bar", "test-support", false, ["tools/Bar/Program.cs"])));
            Write(CommonExecutionEvidence.CheckManifestPath, CommonCheckRegistrationFixture.Manifest(Foo));
        }
        internal void CommitPlan()
        {
            Git("add", ".");
            Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "--allow-empty", "-qm", "resource fixture");
            Commit = Git("rev-parse", "HEAD");
            var entry = Git("ls-tree", "HEAD", "--", changed).Split([' ', '\t'], StringSplitOptions.RemoveEmptyEntries);
            Write("build/changes.json", JsonSerializer.Serialize(new { schema_version = 1, mode = "current",
                candidate = new { commit = Commit, tree = Git("rev-parse", "HEAD^{tree}") }, @base = (string?)null, head = (string?)null,
                complete = true, change_count = 1, changes = new[] { new { status = "A", old = (object?)null, @new = new { path = changed, mode = entry[0], oid = entry[2] } } } }));
            var result = SharedBuildContractTests.Process(Root, "python3", ["-B", "tools/scripts/workflow/ci.py", "plan", "--repository", Root, "--commit", Commit, "--changes", Changes, "--output", Plan],
                hangGuard: TestBudgets.ScriptProcessHangGuard);
            Assert.True(result.Exit == 0, result.Text);
        }
        internal void InputOnlyProjects()
        {
            var registry = File.ReadAllText(Path.Combine(Root, EngineeringRegistrationFixture.Path));
            var checks = JsonNode.Parse(File.ReadAllText(Path.Combine(Root, CommonExecutionEvidence.CheckManifestPath)))!;
            foreach (var (name, role) in new[] { ("Proof", "compile-fail-proof"), ("ScriptTests", "cross-cutting-test") })
            {
                var project = $"tools/{name}/{name}.csproj";
                var input = $"tools/{name}/MustNotBuild.cs";
                Write(project, "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><TargetFramework>net10.0</TargetFramework></PropertyGroup></Project>");
                Write(input, "this registered input deliberately cannot compile");
                registry = EngineeringRegistrationFixture.Append(registry, new EngineeringProjectFixture(project, name, role, false, [input]));
                checks["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == "filemap")!["program_projects"]!.AsArray().Add(project);
            }
            Write(EngineeringRegistrationFixture.Path, registry);
            Write(CommonExecutionEvidence.CheckManifestPath, checks.ToJsonString());
            CommitPlan();
        }
        internal void PrPlan()
        {
            var baseline = Commit;
            Write(changed, "changed candidate input\n");
            Git("add", ".");
            Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "triggering head");
            var head = Git("rev-parse", "HEAD");
            Commit = Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit-tree",
                Git("rev-parse", "HEAD^{tree}"), "-p", baseline, "-p", head, "-m", "candidate merge");
            Git("reset", "--hard", Commit);
            var scope = SharedBuildContractTests.Process(Root, "python3", ["-B", "tools/scripts/workflow/ci.py", "pr-paths",
                "--repository", Root, "--commit", Commit, "--base", baseline, "--head", head, "--output", Changes]);
            Assert.True(scope.Exit == 0, scope.Text);
            var plan = SharedBuildContractTests.Process(Root, "python3", ["-B", "tools/scripts/workflow/ci.py", "plan",
                "--repository", Root, "--commit", Commit, "--changes", Changes, "--output", Plan]);
            Assert.True(plan.Exit == 0, plan.Text);
        }
        internal int Run(string stage, TextWriter output, bool planned = true)
        {
            var executable = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
            var result = SharedBuildContractTests.Process(Root, executable,
                [stage, "--repository", Root, .. planned ? new[] { "--plan", Plan, "--changes", Changes } : []],
                new Dictionary<string, string> { ["PATH"] = processPath! }, TestBudgets.WorkflowProcessHangGuard);
            output.Write(result.Text);
            if (Environment.GetEnvironmentVariable("CI_RESOURCE_ROUTE_EVIDENCE") is { Length: > 0 } evidence)
                File.AppendAllText(evidence, JsonSerializer.Serialize(new { stage, planned, required, result.Exit,
                    processes = result.Text.Split('\n').Where(line => line.StartsWith("STAGE_PROCESS ", StringComparison.Ordinal))
                        .Select(line => JsonNode.Parse(line["STAGE_PROCESS ".Length..])).ToArray() }) + "\n");
            return result.Exit;
        }
        internal void CompleteCheckBoundary(string[]? ids = null)
        {
            // The child boundary replays an actual H2 fixture producer record. Native
            // current must consume its 22 units and represent each original obligation.
            CheckEvidenceFixture.Seal(Root, "current", CommonExecutionEvidence.ValidateBuild(Root), ids);
            File.Copy(Path.Combine(Root, CommonExecutionEvidence.ChecksPath("current")), Path.Combine(Root, "build/produced-checks.json"), true);
            Executable("build/bin/dotnet", "printf 'dotnet check-current\n' >> build/launched\ncp build/produced-checks.json build/ci/current-checks.json\n");
        }
        internal void FilemapFailure() => Executable("build/bin/dotnet", "printf 'dotnet filemap-conform\n' >> build/launched\nexit 1\n");
        internal void Processes(bool prepareReport = true)
        {
            Executable("build/bin/dotnet", "printf 'dotnet filemap-conform\n' >> build/launched\n[[ \"$*\" == *filemap-conform ]]\n");
            Executable("build/bin/make", "printf 'make %s\n' \"$*\" >> build/launched\n");
            processPath = Path.Combine(Root, "build/bin") + Path.PathSeparator + processPath;
            foreach (var binary in new[] { CommonExecutionEvidence.CliPath, CommonExecutionEvidence.LeanProducerPath }) Write(binary, "fixture binary");
            Write("build/ci/log", "fixture build");
            CommonExecutionEvidence.SealBuild(Root, CommonExecutionEvidence.Candidate(Root),
                [CommonExecutionEvidence.CliPath, CommonExecutionEvidence.LeanProducerPath],
                CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", "build/ci/log")).ToArray());
            if (prepareReport && required.Any(id => id is "lean-report" or "scribe" or "current")) Report();
        }
        internal void Report() => CiTransportTests.Report(fixture.Root);
        internal void Write(string path, string text) => fixture.Write(path, text);
        private void Executable(string path, string text)
        {
            Write(path, "#!/bin/bash\nset -euo pipefail\n" + text);
            if (!OperatingSystem.IsWindows()) File.SetUnixFileMode(Path.Combine(Root, path), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }
        private string Git(params string[] arguments)
        {
            var result = SharedBuildContractTests.Process(Root, "git", arguments, hangGuard: TestBudgets.ScriptProcessHangGuard);
            Assert.True(result.Exit == 0, result.Text);
            return result.Text.Trim();
        }
        public void Dispose() => fixture.Dispose();
    }
}
