using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Tests;

internal sealed class JudgeSeedFixture : IDisposable
{
    private readonly TemporaryDirectory temporary = new();
    private readonly string producerRoot = TestRepositoryLayout.FindRoot();
    private readonly Dictionary<string, string> environment = new()
    {
        ["MSBUILDDISABLENODEREUSE"] = "1", ["DOTNET_CLI_DO_NOT_USE_MSBUILD_SERVER"] = "1",
        ["CI"] = "true", ["DOTNET_CLI_UI_LANGUAGE"] = "en-US", ["GITHUB_RUN_ID"] = "17",
        ["GITHUB_RUN_ATTEMPT"] = "2", ["GITHUB_EVENT_NAME"] = "push", ["GITHUB_REF"] = "refs/heads/dev",
        ["STRATALINT_CACHE_WRITES"] = "true", ["STRATALINT_CHECK_SUCCEEDED"] = "false",
        ["STRATALINT_BUILD_SUCCEEDED"] = "true", ["CustomAfterMicrosoftCSharpTargets"] = "",
    };
    private string root;
    private int sequence;
    private string? snapshotPath;
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
    }

    internal string PathOf(string relative) => Path.Combine(root, relative);
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

    internal Invocation Dotnet(string[] args, bool success = true) => Run("dotnet", args, success);
    internal void Build(string name, int expected, params string[] properties) => BuildProject(name, "tools/StrataLint.sln", expected, properties);
    internal void BuildHelper(string name, int expected) => BuildProject(name, "tools/scripts/report/JudgeSeedTask.csproj", expected, []);
    private void BuildProject(string name, string project, int expected, string[] properties)
    {
        Dotnet(["restore", project, "--locked-mode"]);
        var result = Dotnet(["build", project, "--no-restore", "--configuration", "Release", "--warnaserror", "-v:diag", ..properties], false);
        var count = Regex.Matches(result.Text, "Task \"Csc\"(?: \\(TaskId:\\d+\\))?").Count;
        Record(name, result, count);
        Assert.True(result.ExitCode == 0, Tail(result.Text));
        Assert.True(expected == count, $"{name}: expected {expected} Csc executions, actual {count}\n{Tail(result.Text)}");
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
        Python("actions.snapshot(root, actions.actions_keys(root), ('judge',))", settings: settings);
    }

    internal void Restore()
    {
        foreach (var project in new[] { "Library", "Consumer" })
        foreach (var kind in new[] { "bin", "obj" })
            if (Directory.Exists(PathOf($"tools/{project}/{kind}"))) Directory.Delete(PathOf($"tools/{project}/{kind}"), true);
        Python("keys=actions.actions_keys(root); actions.restore(root, keys, {'judge':keys['judge']['key']}, ('judge',))");
        // Perturb checkout times relative to the transported material, as a
        // checkout does. A future year would keep cold compiler outputs stale.
        var stamp = Directory.GetFiles(root, "*.dll", SearchOption.AllDirectories)
            .Select(File.GetLastWriteTimeUtc).Max().AddTicks(10);
        foreach (var path in new[] { "global.json", "Directory.Build.props", "tools/Library/Library.csproj", "tools/Library/Code.cs",
                     "tools/Consumer/Consumer.csproj", "tools/Consumer/Program.cs" }) File.SetLastWriteTimeUtc(PathOf(path), stamp);
        Prepare();
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
        var receipt = PathOf("build/judge-seed/receipts/Library.csproj.seed.json");
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
        Write(".gitignore", "build/\n**/bin/\n**/obj/\n");
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
