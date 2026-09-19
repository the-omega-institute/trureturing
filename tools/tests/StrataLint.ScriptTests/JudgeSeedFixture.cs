using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Text.RegularExpressions;

namespace StrataLint.Tests;

internal sealed class JudgeSeedFixture : IDisposable
{
    private readonly TemporaryDirectory temporary = new();
    private readonly string producerRoot = TestRepositoryLayout.FindRoot();
    private readonly Dictionary<string, string> environment = new()
    {
        ["CI"] = "true", ["DOTNET_CLI_UI_LANGUAGE"] = "en-US", ["GITHUB_RUN_ID"] = "17",
        ["GITHUB_RUN_ATTEMPT"] = "2", ["GITHUB_EVENT_NAME"] = "push", ["GITHUB_REF"] = "refs/heads/dev",
        ["STRATALINT_CACHE_WRITES"] = "true", ["STRATALINT_CHECK_SUCCEEDED"] = "false",
        ["STRATALINT_BUILD_SUCCEEDED"] = "true", ["CustomAfterMicrosoftCSharpTargets"] = "",
    };
    private string root;
    private int sequence;
    private string? snapshotPath;
    private string[] projectFiles = ["tools/Library/Library.csproj", "tools/Consumer/Consumer.csproj"];
    internal string SnapshotManifest => PathOf((snapshotPath ?? throw new InvalidOperationException()) + "/manifest.json");

    internal JudgeSeedFixture()
    {
        root = Path.Combine(temporary.Path, "repository");
        Directory.CreateDirectory(root);
        Write("global.json", File.ReadAllText(Path.Combine(producerRoot, "global.json")));
        // Synthetic registration is also used for the pre-implementation red run.
        Write("Meta/judge-seed.json", JsonSerializer.Serialize(new
        {
            version = 1, sdk_version = "10.0.103", target_framework = "net10.0",
            sdk_files = new[] { "Roslyn/bincore/csc.dll", "Roslyn/bincore/csc.deps.json", "Roslyn/bincore/csc.runtimeconfig.json",
                "Roslyn/bincore/Microsoft.CodeAnalysis.dll", "Roslyn/bincore/Microsoft.CodeAnalysis.CSharp.dll",
                "Roslyn/Microsoft.Build.Tasks.CodeAnalysis.dll", "Microsoft.Build.dll", "Microsoft.Build.Framework.dll",
                "Microsoft.Build.Utilities.Core.dll", "Microsoft.Build.Tasks.Core.dll", "dotnet.runtimeconfig.json" },
            repository_files = new[] { "Directory.Build.props" },
        }));
        Write("lake-manifest.json", JsonSerializer.Serialize(new { packages = new[] { new { name = "mathlib", rev = new string('a', 40) } } }));
        Write("Directory.Build.props", "<Project><PropertyGroup><TargetFramework>net10.0</TargetFramework><RestorePackagesWithLockFile>true</RestorePackagesWithLockFile><Deterministic>true</Deterministic></PropertyGroup></Project>");
        Write("tools/Library/Library.csproj", "<Project Sdk=\"Microsoft.NET.Sdk\"><ItemGroup><EmbeddedResource Include=\"message.txt\" LogicalName=\"message\"/><AdditionalFiles Include=\"generator-input.txt\"/></ItemGroup></Project>");
        Write("tools/Library/Code.cs", "public static class Library { public static int Value() => 1; }");
        Write("tools/Library/message.txt", "first resource");
        Write("tools/Library/generator-input.txt", "first additional input");
        Write("tools/Consumer/Consumer.csproj", "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><OutputType>Exe</OutputType></PropertyGroup><ItemGroup><ProjectReference Include=\"../Library/Library.csproj\"/><None Update=\"data.sh\" CopyToOutputDirectory=\"PreserveNewest\"/></ItemGroup></Project>");
        Write("tools/Consumer/Program.cs", "System.Console.WriteLine(Library.Value());");
        Write("tools/Consumer/data.sh", "echo first\n");
        Dotnet(["new", "sln", "--format", "sln", "--name", "StrataLint", "--output", "tools"]);
        Dotnet(["sln", "tools/StrataLint.sln", "add", "tools/Library/Library.csproj", "tools/Consumer/Consumer.csproj"]);
        Dotnet(["restore", "tools/StrataLint.sln", "--use-lock-file"]);
        Write("Meta/engineering-projects.json", JsonSerializer.Serialize(new
        {
            version = 1, test_parallelism = 1, rule_build_inputs = Array.Empty<string>(), projects = new[]
            {
                ProjectRow("tools/Library/Library.csproj", "Library", "test-support", ["tools/Library/**/*.cs"], []),
                ProjectRow("tools/Consumer/Consumer.csproj", "Consumer", "test-support", ["tools/Consumer/**/*.cs"], ["tools/Library/Library.csproj"]),
            }, historical_projects = Array.Empty<object>(),
        }));
        Write(".gitignore", "build/\n**/bin/\n**/obj/\n.judge-binaries/\n");
        Directory.CreateDirectory(PathOf("build/empty-git-config"));
        Git("init", "--quiet", "--template=" + PathOf("build/empty-git-config"));
        Git("add", ".");
    }

    internal static object ProjectRow(string path, string assembly, string role, string[] include, string[] references) => new
    {
        path, assembly, role, ci = false, include, exclude = Array.Empty<string>(), references,
        owner = (object?)null, owned_test_assembly = role == "production" ? assembly + ".Tests" : null,
        test_partition = (string?)null,
        root_namespace = assembly, namespace_exclude = Array.Empty<string>(), global_namespace_exceptions = Array.Empty<string>(),
        build_inputs = Array.Empty<string>(), execution_inputs = (string[]?)null,
        execution_excludes = (string[]?)null, execution_environment = (string[]?)null,
    };

    internal void NativePushCandidate()
    {
        // Push must see the production ignore policy, including any omissions.
        File.Copy(Path.Combine(producerRoot, ".gitignore"), PathOf(".gitignore"), overwrite: true);
        var canonical = JsonNode.Parse(File.ReadAllText(Path.Combine(producerRoot,
            "tools/tests/StrataLint.Tests/Commands/FileMapPlanning/canonical.json")))!;
        Write("Meta/FILEMAP.toml", canonical["filemap"]!.GetValue<string>().Replace("materials = []",
            "materials = [\"Meta/ci-checks.json\", \"Meta/ci-resources.json\", \"Meta/engineering-projects.json\"]",
            StringComparison.Ordinal).Replace("pattern = \"Meta/FILEMAP.toml\"", "pattern = \"Meta/*\"", StringComparison.Ordinal));
        const string project = "tools/Consumer/Consumer.csproj";
        Write("Meta/ci-checks.json", CommonCheckRegistrationFixture.Manifest(project));
        Write("Meta/ci-resources.json", JsonSerializer.Serialize(new { schema = "ci-resource-execution-v1",
            resources = new[] {
                new { id = "build", projects = new[] { project }, checks = Array.Empty<string>(), steps = Array.Empty<string>() },
                new { id = "engineering", projects = new[] { project }, checks = Array.Empty<string>(), steps = Array.Empty<string>() },
                new { id = "filemap", projects = new[] { project }, checks = new[] { "filemap" }, steps = new[] { "filemap" } },
                new { id = "lean-report", projects = new[] { project }, checks = Array.Empty<string>(), steps = new[] { "lean-report" } },
            } }));
        Write("tools/owner.py", "# synthetic registered operation owner\n");
        Git("add", ".");
        Git("commit", "--quiet", "-m", "native push baseline");
        var before = Git("rev-parse", "HEAD").Text.Trim();
        Write("tools/Library/Code.cs", "public static class Library { public static int Value() => 2; }\n");
        Git("add", "tools/Library/Code.cs");
        Git("commit", "--quiet", "-m", "native push candidate");
        var after = Git("rev-parse", "HEAD").Text.Trim();
        environment["GITHUB_EVENT_PATH"] = Write("build/native-push-event.json", JsonSerializer.Serialize(new { before, after }));
        environment["CANDIDATE_SHA"] = after;
        environment["CI_WORKFLOW_INPUTS"] = "null";
        environment["CI_NEEDS"] = "{}";
        foreach (var name in new[] { "CI_PLAN_PATH", "CI_CHANGES_PATH",
                     "CI_PUSH_BEFORE", "CI_PUSH_AFTER", "GITHUB_OUTPUT" }) environment[name] = "";
    }

    internal Invocation PushStageInput() => Run("python3",
        ["-B", Path.Combine(producerRoot, "tools/scripts/workflow/ci.py"), "stage-input", "--repository", root,
            "--stage", "build", "--plan", "build/ci/plan.json", "--changes", "build/ci/changes.json"], false);

    internal void EditProjects(Action<JsonObject> change)
    {
        var registry = JsonNode.Parse(File.ReadAllText(PathOf("Meta/engineering-projects.json")))!.AsObject();
        change(registry);
        Write("Meta/engineering-projects.json", registry.ToJsonString());
    }

    internal string PathOf(string relative) => Path.Combine(root, relative);

    internal string AddPrivateSdkReference()
    {
        var source = Path.Combine(Environment.GetEnvironmentVariable("DOTNET_ROOT")
            ?? throw new InvalidOperationException("DOTNET_ROOT is required for the pinned SDK fixture"),
            "sdk", "10.0.103", "Microsoft.Build.dll");
        var reference = Path.Combine(temporary.Path, "sdk-reference", "Microsoft.Build.dll");
        Directory.CreateDirectory(Path.GetDirectoryName(reference)!);
        File.Copy(source, reference);
        const string project = "tools/Library/Library.csproj";
        Write(project, File.ReadAllText(PathOf(project)).Replace("</Project>",
            $"<ItemGroup><Reference Include=\"Microsoft.Build\"><HintPath>{System.Security.SecurityElement.Escape(reference)}</HintPath><Private>false</Private></Reference></ItemGroup></Project>",
            StringComparison.Ordinal));
        return reference;
    }

    internal void RecordPrivateReference(string name, string reference)
    {
        var capturePath = PathOf("tools/Library/obj/Release/net10.0/judge-seed-inputs.xml");
        var captured = File.Exists(capturePath)
            ? System.Xml.Linq.XDocument.Load(capturePath).Root!.Element("inputs")!.Elements("file").Any(item => item.Value == reference)
            : (bool?)null;
        var receipt = JsonNode.Parse(File.ReadAllText(PathOf("build/judge-seed/receipts/tools/Library/Library.csproj.seed.json")));
        Assert.NotNull(receipt!["inputs"]![reference]);
        if (captured.HasValue) Assert.True(captured.Value);
        Record(name, new Invocation(0, JsonSerializer.Serialize(new
        {
            reference, sha256 = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(reference))),
            reference_time = File.GetLastWriteTimeUtc(reference),
            captured,
            receipt_input = receipt!["inputs"]![reference],
        })), null);
    }

    internal string Write(string relative, string text)
    {
        var path = PathOf(relative);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, text);
        return path;
    }

    internal void WritePreservingTime(string relative, string text)
    {
        var stamp = File.GetLastWriteTimeUtc(PathOf(relative));
        Write(relative, text);
        File.SetLastWriteTimeUtc(PathOf(relative), stamp);
    }

    internal Invocation Prepare(bool success = true)
    {
        var result = Python("judge.prepare_seed(root)", success);
        environment["CustomAfterMicrosoftCSharpTargets"] = PathOf("build/judge-seed/seed.targets");
        return result;
    }

    internal Invocation PrepareWithoutHelper()
    {
        Directory.Delete(PathOf("build/judge-seed/task/bin"), recursive: true);
        return Python("judge.prepare_task = lambda *_: (_ for _ in ()).throw(OSError('fixture helper unavailable')); judge.prepare_seed(root)");
    }

    internal string[] CompilerObservation()
    {
        var result = Run("python3", [Path.Combine(producerRoot, "tools/scripts/report/dotnet_producer.py"), "compiler-logger", root]);
        var assembly = result.Text.Trim();
        return assembly.Length == 0 ? [] : ["-logger:StrataLint.JudgeSeed.CscExecutionLogger," + assembly];
    }

    // Only owned MSBuild invocations disable node reuse; DLL/CLI calls retain
    // their normal arguments and the producer must own its own child options.
    internal Invocation Dotnet(string[] args, bool success = true) =>
        Run("dotnet", args[0] is "restore" or "build" ? [..args, "-nr:false"] : args, success);
    internal Invocation Build(string name, int expected, params string[] properties) => BuildProject(name, "tools/StrataLint.sln", expected, properties);
    internal void BuildHelper(string name, int expected) => BuildProject(name, "tools/scripts/report/JudgeSeedTask.csproj", expected, []);

    internal Invocation[] BuildRegisteredProjects(string name)
    {
        var results = new List<Invocation>();
        var observation = CompilerObservation();
        foreach (var project in projectFiles)
        {
            Dotnet(["restore", project, "--locked-mode"]);
            var result = Dotnet(["build", project, "--no-restore", "--configuration", "Release",
                "--warnaserror", "-v:diag", .. observation], false);
            Record(name + "-" + Path.GetFileName(project), result,
                Regex.Matches(result.Text, "Task \"Csc\"(?: \\(TaskId:\\d+\\))?").Count);
            Assert.True(result.ExitCode == 0, Tail(result.Text));
            results.Add(result);
        }
        Write("build/ci/build.json", JsonSerializer.Serialize(new { version = 2, projects = projectFiles }));
        return results.ToArray();
    }

    internal void RenewGeneratedNuGetImportTimes()
    {
        foreach (var project in projectFiles)
        {
            var path = PathOf(Path.GetDirectoryName(project) + "/obj/" + Path.GetFileName(project) + ".nuget.g.props");
            var bytes = File.ReadAllBytes(path);
            var output = PathOf(Path.GetDirectoryName(project) + "/obj/Release/net10.0/"
                + Path.GetFileNameWithoutExtension(project) + ".dll");
            var stamp = File.GetLastWriteTimeUtc(output).AddMilliseconds(1);
            File.SetLastWriteTimeUtc(path, stamp);
            Assert.Equal(bytes, File.ReadAllBytes(path));
            Assert.True(File.GetLastWriteTimeUtc(path) > File.GetLastWriteTimeUtc(output));
            Record("renew-import-" + Path.GetFileName(project), new Invocation(0, JsonSerializer.Serialize(new
            {
                path, sha256 = Convert.ToHexStringLower(SHA256.HashData(bytes)),
                import_time = File.GetLastWriteTimeUtc(path), output_time = File.GetLastWriteTimeUtc(output),
            })), null);
        }
    }

    private Invocation BuildProject(string name, string project, int expected, string[] properties)
    {
        Dotnet(["restore", project, "--locked-mode"]);
        var result = Dotnet(["build", project, "--no-restore", "--configuration", "Release", "--warnaserror", "-v:diag", ..properties], false);
        var count = Regex.Matches(result.Text, "Task \"Csc\"(?: \\(TaskId:\\d+\\))?").Count;
        Record(name, result, count);
        Assert.True(result.ExitCode == 0, Tail(result.Text));
        Assert.True(expected == count, $"{name}: expected {expected} Csc executions, actual {count}\n{Tail(result.Text)}");
        // Retain the explicitly requested, successful fixture build roots for
        // the same seed adapter used by the native shared build.
        Write("build/ci/build.json", JsonSerializer.Serialize(new
        {
            version = 2, projects = project == "tools/StrataLint.sln" ? projectFiles : [project],
        }));
        return result;
    }

    internal Invocation BuildFailure(string name)
    {
        var result = Dotnet(["build", "tools/StrataLint.sln", "--configuration", "Release", "--warnaserror"], false);
        Record(name, result, null);
        return result;
    }

    internal string Dll(string project, string? name = null) => PathOf($"tools/{project}/bin/Release/net10.0/{name ?? project}.dll");
    internal string[] Products() => new[] { "Library", "Consumer" }.SelectMany(project => Directory.GetFiles(Path.GetDirectoryName(Dll(project))!))
        .Order(StringComparer.Ordinal).Select(path => Path.GetRelativePath(root, path) + ":" + Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(path)))).ToArray();

    internal void Snapshot(params string[] settings)
    {
        var keys = JsonDocument.Parse(Python("print(json.dumps(actions.actions_keys(root)))").Text);
        Assert.False(keys.RootElement.GetProperty("save_allowed").GetBoolean());
        snapshotPath = keys.RootElement.GetProperty("judge").GetProperty("path").GetString()!;
        if (Directory.Exists(PathOf(snapshotPath))) Directory.Delete(PathOf(snapshotPath), true);
        var result = Python("actions.snapshot(root, actions.actions_keys(root), ('judge',))", settings: settings);
        Record("snapshot", result, null);
    }

    internal void Restore()
    {
        foreach (var project in new[] { "Library", "Consumer" })
        foreach (var kind in new[] { "bin", "obj" })
            if (Directory.Exists(PathOf($"tools/{project}/{kind}"))) Directory.Delete(PathOf($"tools/{project}/{kind}"), true);
        RestoreTransport();
        // Perturb checkout times relative to the transported material, as a
        // checkout does. A future year would keep cold compiler outputs stale.
        var stamp = Directory.GetFiles(root, "*.dll", SearchOption.AllDirectories)
            .Select(File.GetLastWriteTimeUtc).Max().AddTicks(10);
        foreach (var path in new[] { "global.json", "Directory.Build.props", "tools/Library/Code.cs",
                     "tools/Consumer/Program.cs" }.Concat(projectFiles)) File.SetLastWriteTimeUtc(PathOf(path), stamp);
        Prepare();
    }

    internal void RestoreTransport()
    {
        var result = Python("keys=actions.actions_keys(root); actions.restore(root, keys, {'judge':keys['judge']['key']}, ('judge',))");
        Record("restore", result, null);
    }

    internal Invocation TransportCommand(string command) => Run("python3",
        [Path.Combine(producerRoot, "tools/scripts/worktree/lean_actions.py"), command, "--repository", root, "--layers", "judge"], false);

    internal JsonObject CacheKeys() => JsonNode.Parse(Python("print(json.dumps(actions.actions_keys(root)))").Text)!.AsObject();

    internal Invocation RestoreLayer(string layer, string key, string? outcome = null) => Run("python3",
        [Path.Combine(producerRoot, "tools/scripts/worktree/lean_actions.py"), "restore", "--repository", root,
            "--layers", layer, "--" + layer + "-key", key,
            .. outcome is null ? Array.Empty<string>() : ["--" + layer + "-outcome", outcome]]);

    internal void AddUnlistedTransportNeighbor() => Write(snapshotPath! + "/data/data/tools/Neighbor/obj/Neighbor.dll", "not in manifest");

    internal void UseSameProjectBasenames()
    {
        foreach (var name in new[] { "Library", "Consumer" })
        {
            var path = PathOf($"tools/{name}/{name}.csproj");
            var contents = File.ReadAllText(path).Replace("</Project>",
                $"<PropertyGroup><AssemblyName>{name}</AssemblyName></PropertyGroup></Project>", StringComparison.Ordinal)
                .Replace("Library.csproj", "Project.csproj", StringComparison.Ordinal);
            File.Delete(path);
            Write($"tools/{name}/Project.csproj", contents);
        }
        var solution = File.ReadAllText(PathOf("tools/StrataLint.sln"));
        Write("tools/StrataLint.sln", solution.Replace("Library.csproj", "Project.csproj", StringComparison.Ordinal)
            .Replace("Consumer.csproj", "Project.csproj", StringComparison.Ordinal));
        projectFiles = ["tools/Library/Project.csproj", "tools/Consumer/Project.csproj"];
        EditProjects(registry =>
        {
            registry["projects"]![0]!["path"] = projectFiles[0];
            registry["projects"]![1]!["path"] = projectFiles[1];
            registry["projects"]![1]!["references"] = new JsonArray(projectFiles[0]);
        });
        Git("add", "tools", "Meta/engineering-projects.json");
    }

    internal void RestoreWithMissingTransferredProject()
    {
        Python("keys=actions.actions_keys(root); actions.restore(root, keys, {'judge':keys['judge']['key']}, ('judge',))");
        Directory.Delete(PathOf(".judge-binaries/data/tools/Consumer/obj"), true);
        Prepare();
    }

    internal void CorruptSnapshot()
    {
        var path = Directory.GetFiles(PathOf(snapshotPath!), "Consumer.dll", SearchOption.AllDirectories).First();
        var stamp = File.GetLastWriteTimeUtc(path);
        File.WriteAllText(path, "corrupt");
        File.SetLastWriteTimeUtc(path, stamp);
    }

    internal void FailSnapshotSave()
    {
        // A real unreadable material shape makes the optional transport fail.
        var receipt = PathOf("build/judge-seed/receipts/tools/Library/Library.csproj.seed.json");
        File.Delete(receipt);
        Directory.CreateDirectory(receipt);
        Snapshot();
    }

    internal void Relocate()
    {
        var destination = Path.Combine(temporary.Path, "relocated");
        CopyTree(root, destination);
        root = destination;
    }

    private static void CopyTree(string source, string destination)
    {
        Directory.CreateDirectory(destination);
        foreach (var file in Directory.GetFiles(source)) File.Copy(file, Path.Combine(destination, Path.GetFileName(file)));
        foreach (var directory in Directory.GetDirectories(source)) CopyTree(directory, Path.Combine(destination, Path.GetFileName(directory)));
    }

    internal void InitializeGit()
    {
        foreach (var path in new[] { "tools/scripts/report/JudgeSeedTask.csproj", "tools/scripts/report/JudgeSeedTask.cs", "tools/scripts/report/packages.lock.json" })
            Write(path, File.ReadAllText(Path.Combine(producerRoot, path)));
        EditProjects(registry => registry["projects"]!.AsArray().Add(JsonSerializer.SerializeToNode(ProjectRow(
            "tools/scripts/report/JudgeSeedTask.csproj", "JudgeSeedTask", "production", ["tools/scripts/report/JudgeSeedTask.cs"], []))));
        Write("README.md", "helper fixture\n");
        Directory.CreateDirectory(PathOf("build/empty-git-config"));
        Git("init", "--quiet", "--template=" + PathOf("build/empty-git-config"));
        Git("add", ".");
        Git("commit", "--quiet", "-m", "helper compiler inputs");
    }

    internal Invocation Git(params string[] args) => Run("git", ["-c", "core.hooksPath=" + PathOf("build/empty-git-config"), "-c", "commit.gpgsign=false",
        "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", ..args]);

    private Invocation Python(string call, bool success = true, params string[] settings) => Run("python3",
        ["-c", "import sys,pathlib,json; sys.path[:0]=sys.argv[1:3]; import dotnet_producer as judge; import lean_actions as actions; root=pathlib.Path(sys.argv[3]); " + call,
            Path.Combine(producerRoot, "tools/scripts/report"), Path.Combine(producerRoot, "tools/scripts/worktree"), root], success, settings);

    private Invocation Run(string executable, string[] args, bool success = true, params string[] settings)
    {
        var variables = environment.Select(pair => pair.Key + "=" + pair.Value).ToList();
        variables.AddRange(settings);
        var result = TestProcessRunner.Run("/usr/bin/env", [..variables, executable, ..args], root,
            TestBudgets.LongWorkflowProcessHangGuard, 16 * 1024 * 1024);
        var invocation = new Invocation(result.ExitCode, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        if (success) Assert.True(invocation.ExitCode == 0, Tail(invocation.Text));
        return invocation;
    }

    private static string Tail(string text) => text.Length > 12000 ? text[^12000..] : text;

    internal Invocation ReadFakeSdkMaterial() => Python("print(json.dumps(judge.seed_registration(root, root / 'extra-sdk')[3]))");

    private void Record(string name, Invocation result, int? csc)
    {
        var evidence = Environment.GetEnvironmentVariable("JUDGE_SEED_EVIDENCE");
        if (string.IsNullOrEmpty(evidence)) return;
        Directory.CreateDirectory(evidence);
        var identity = Path.GetFileName(temporary.Path) + "-" + sequence++ + "-" + name;
        File.WriteAllText(Path.Combine(evidence, identity + ".log"), result.Text);
        File.WriteAllText(Path.Combine(evidence, identity + ".json"), JsonSerializer.Serialize(new { name, exit = result.ExitCode, csc_tasks = csc }));
    }

    public void Dispose() => temporary.Dispose();
    internal sealed record Invocation(int ExitCode, string Text);
}
