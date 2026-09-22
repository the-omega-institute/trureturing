using System.Diagnostics;
using System.Formats.Tar;
using System.IO.Compression;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Xml.Linq;
using StrataLint.EngineeringScope;
using Xunit;
using static StrataLint.TestSupport.ExecutionFixture;

namespace StrataLint.TestSupport;

internal sealed class ResourceFixture : IDisposable
{
    internal const string Foo = "tools/Foo/Foo.csproj";
    internal const string Bar = "tools/Bar/Bar.csproj";
    private readonly CiFixtureEnvironment environment;
    private readonly ExecutionFixture fixture = new();
    private string? processPath = Environment.GetEnvironmentVariable("PATH");
    private readonly string? physicalRoot;
    internal string Root => physicalRoot ?? fixture.Root;
    internal IReadOnlyDictionary<string, string> DotnetProfile() => DotnetFixtureProfile.Create(fixture.Root);
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
        // The seed projects are retired below. Register their real old
        // tree before creating the resource candidate that deletes them.
        Write("Meta/FILEMAP.toml", """
            schema_version = 4
            resources = []
            [residence_policy]
            case_id = "FIXTURE"
            desired = "registered"
            known_violation_count = 0
            status = "closed"
            [[files]]
            pattern = "**"
            require = []
            kind = "program"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["test"]
            verified_by = ["test"]
            artifact_id = "none"
            runtime_disposition = "committed-source"
            """ + "\n");
        Git("add", "Meta/FILEMAP.toml");
        Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "register seed projects");
        var source = TestRepositoryLayout.FindRoot();
        foreach (var path in new[] { "tools/scripts/workflow/ci.py", "tools/scripts/workflow/ci_plan.py", "tools/scripts/ci-build-outputs.targets" })
            Write(path, File.ReadAllText(Path.Combine(source, path)));
        Write(changed, "registered input\n");
        Write(".gitignore", "build/\n.lake/\n**/bin/\n**/obj/\n__pycache__/\n");
        foreach (var path in new[] { ExecutionFixture.First, ExecutionFixture.Second,
            "tools/tests/CompileFailProof/CompileFailProof.csproj", "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj",
            "tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs" })
            File.Delete(Path.Combine(Root, path));
        Write(PackageMaterialRegistry.RelativePath, JsonSerializer.Serialize(new {
            schemaVersion = 1, packageRootSource = "build-output:NuGetPackageRoot",
            packages = new[] { new { packagePath = "xunit/2.9.3", include = new[] { "xunit.nuspec" }, exclude = Array.Empty<string>() } } }));
        Register();
        CommitPlan();
        environment = new CiFixtureEnvironment();
    }
    private void Register()
    {
        var mapping = new[] {
            new { id = "build", projects = Array.Empty<string>(), checks = Array.Empty<string>(), steps = Array.Empty<string>() },
            new { id = "filemap", projects = new[] { Foo }, checks = new[] { "filemap" }, steps = new[] { "filemap" } },
            new { id = "lean", projects = new[] { Bar }, checks = Array.Empty<string>(), steps = new[] { "lean" } },
            new { id = "lean-inspector-build", projects = Array.Empty<string>(), checks = Array.Empty<string>(), steps = Array.Empty<string>() },
            new { id = "lean-report", projects = new[] { Bar }, checks = Array.Empty<string>(), steps = new[] { "lean-report" } },
            new { id = "scribe", projects = new[] { Foo }, checks = new[] { "scribe-describe", "scribe-markdown", "scribe-projections" }, steps = new[] { "scribe" } },
            new { id = "current", projects = new[] { Foo }, checks = new[] { "SL-015" }, steps = new[] { "check-current" } }
        };
        var manifest = JsonSerializer.SerializeToNode(new { schema = "ci-resource-execution-v1", resources = mapping })!;
        manifest["resources"]!.AsArray().Single(row => row!["id"]!.ToString() == "lean-inspector-build")!["lean_targets"] = new JsonArray("FixtureAudit", "fixture/inspector");
        Write("Meta/ci-resources.json", manifest.ToJsonString());
        var rows = mapping.OrderBy(row => row.id, StringComparer.Ordinal).Select(row =>
            "  { id = \"" + row.id + "\", stage = \"" + (row.id == "build" ? "build" : "current")
            + "\", owner = \"tools/scripts/workflow/ci.py\", prerequisites = " + (row.id == "build" ? "[]" : row.id == "lean-report" ? "[\"lean\"]" : row.id is "scribe" or "current" or "lean-inspector-build" ? "[\"lean-report\"]" : "[\"build\"]")
            + ", tools = [], cache_layers = [], cache_activation = {}, materials = [\"Meta/ci-checks.json\", \"Meta/ci-resources.json\", \"Meta/engineering-projects.json\"] },");
        Write("Meta/FILEMAP.toml", "schema_version = 4\nresources = [\n" + string.Join("\n", rows) + "\n]\n"
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
        var scopeManifest = JsonNode.Parse(File.ReadAllText(Path.Combine(Root, CommonExecutionEvidence.CheckManifestPath)))!;
        scopeManifest["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == "filemap")!["delta_scope"] = JsonNode.Parse("""
            {"whole_tree_inputs":["Meta/FILEMAP.toml"],"actor_inputs":["tools/**/*.cs"],"inventory_inputs":["Blueprint/**"],"related":[]}
            """);
        var markdown = scopeManifest["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == "scribe-markdown")!;
        markdown["path_inventory"] = new JsonArray("Blueprint/**/*.md");
        markdown["markdown_scope"] = JsonNode.Parse("""
            {"whole_tree_inputs":["tools/Renderer/**"],"changed_inputs":["Blueprint/**/*.md","Blueprint/**/*.scribe.cs"]}
            """);
        Write(CommonExecutionEvidence.CheckManifestPath, scopeManifest.ToJsonString());
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
        var result = EngineeringProcess.Process(Root, "python3", ["-B", "tools/scripts/workflow/ci.py", "plan", "--repository", Root, "--commit", Commit, "--changes", Changes, "--output", Plan],
            hangGuard: TestBudgets.ScriptProcessHangGuard);
        Assert.True(result.Exit == 0, result.Text);
    }
    internal void RemoveObject(string oid)
    {
        var result = EngineeringProcess.Process(Root, "python3", ["-c", """
            import os, pathlib, subprocess, sys, tempfile
            environment = {**os.environ, 'GIT_NO_LAZY_FETCH': '1'}
            def git(*arguments, **options):
                return subprocess.run(['git', '-c', 'protocol.allow=never', *arguments],
                    env=environment, check=True, stdout=subprocess.PIPE, **options).stdout
            def inventory():
                return set(git('cat-file', '--batch-all-objects', '--batch-check=%(objectname)').decode().splitlines())
            oid = sys.argv[1]
            before = inventory()
            assert oid in before, 'Fixture object was already unavailable: ' + oid
            objects = pathlib.Path(git('rev-parse', '--git-path', 'objects').decode().strip())
            # Git maintenance may have packed the designated object. Move the
            # packs out of the object database so unpack-objects restores them.
            with tempfile.TemporaryDirectory(dir='build') as temporary:
                packs = objects / 'pack'
                if packs.exists():
                    saved = pathlib.Path(temporary) / 'pack'
                    packs.rename(saved)
                    for pack in saved.glob('*.pack'):
                        with pack.open('rb') as stream:
                            git('unpack-objects', stdin=stream)
                (objects / oid[:2] / oid[2:]).unlink()
                assert inventory() == before - {oid}, 'Fixture removed the wrong object set'
            missing = subprocess.run(['git', '-c', 'protocol.allow=never', 'cat-file', '-e', oid],
                env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            assert missing.returncode == 1, (missing.returncode, missing.stderr)
            """, oid]);
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
        var scope = EngineeringProcess.Process(Root, "python3", ["-B", "tools/scripts/workflow/ci.py", "pr-paths",
            "--repository", Root, "--commit", Commit, "--base", baseline, "--head", head, "--output", Changes]);
        Assert.True(scope.Exit == 0, scope.Text);
        var plan = EngineeringProcess.Process(Root, "python3", ["-B", "tools/scripts/workflow/ci.py", "plan",
            "--repository", Root, "--commit", Commit, "--changes", Changes, "--output", Plan]);
        Assert.True(plan.Exit == 0, plan.Text);
    }
    internal int Run(string stage, TextWriter output, bool planned = true)
    {
        var executable = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
        var result = EngineeringProcess.Process(Root, executable,
            [stage, "--repository", Root, .. planned ? new[] { "--plan", Plan, "--changes", Changes } : [],
                .. stage == "delta" ? new[] { "--base", JsonNode.Parse(File.ReadAllText(Plan))!["base"]!.ToString() } : []],
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
        // current must consume every registered unit and represent each original obligation.
        CheckEvidenceFixture.Seal(Root, "current", CommonExecutionEvidence.ValidateBuild(Root), ids);
        File.Copy(Path.Combine(Root, CommonExecutionEvidence.ChecksPath("current")), Path.Combine(Root, "build/produced-checks.json"), true);
        Executable("build/bin/dotnet", "printf 'dotnet check-current\n' >> build/launched\ncp build/produced-checks.json build/ci/current-checks.json\n");
    }
    internal void FilemapFailure() => Executable("build/bin/dotnet", "printf 'dotnet filemap-conform\n' >> build/launched\nexit 1\n");
    internal void Processes(bool prepareReport = true, bool bindPlan = true)
    {
        Executable("build/bin/dotnet", "printf 'dotnet filemap-conform\n' >> build/launched\n[[ \"$*\" == *'filemap-conform --scope build/ci/filemap-scope.json' ]]\n");
        Executable("build/bin/make", "printf 'make %s\n' \"$*\" >> build/launched\n");
        processPath = Path.Combine(Root, "build/bin") + Path.PathSeparator + processPath;
        foreach (var binary in new[] { CommonExecutionEvidence.CliPath, CommonExecutionEvidence.LeanProducerPath }) Write(binary, "fixture binary");
        Write("build/ci/log", "fixture build");
        var plan = bindPlan ? ResourceExecutionPlan.Load(Root, Plan, Changes) : null;
        CommonExecutionEvidence.SealBuild(Root, CommonExecutionEvidence.Candidate(Root),
            [CommonExecutionEvidence.CliPath, CommonExecutionEvidence.LeanProducerPath],
            CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", "build/ci/log")).ToArray(),
            plan?.Projects, plan?.Retain(Root, CommonExecutionEvidence.RootPath));
        if (prepareReport && required.Any(id => id is "lean-report" or "scribe" or "current" or "lean-inspector-build")) Report();
    }
    internal void Report() => ExecutionFixture.Report(fixture.Root);
    internal void Write(string path, string text) => fixture.Write(path, text);
    private void Executable(string path, string text)
    {
        Write(path, "#!/bin/bash\nset -euo pipefail\n" + text);
        if (!OperatingSystem.IsWindows()) File.SetUnixFileMode(Path.Combine(Root, path), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }
    private string Git(params string[] arguments)
    {
        var result = EngineeringProcess.Process(Root, "git", arguments, hangGuard: TestBudgets.ScriptProcessHangGuard);
        Assert.True(result.Exit == 0, result.Text);
        return result.Text.Trim();
    }
    public void Dispose()
    {
        try { fixture.Dispose(); }
        finally { environment.Dispose(); }
    }
}
