using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

// A real compiler + xUnit fixture. Only the unrelated host entrypoint projects
// are empty: this fixture makes no claim about Lean or selftest execution.
internal sealed class AffectedExecutionFixture : IDisposable
{
    internal const string First = "tools/tests/StrataLint.First/StrataLint.First.csproj";
    internal const string Second = "tools/tests/StrataLint.Second/StrataLint.Second.csproj";
    internal string Root { get; } = TemporaryFileSystem.Directory.CreateTempSubdirectory("affected-runtime-").FullName;
    internal StringWriter Output { get; } = new();
    private int buildNumber;
    private int testNumber;
    internal string CacheDirectory => Path.GetDirectoryName(Directory.GetFiles(Path.Combine(Root, AffectedTestCache.CachePath), "seed.json", SearchOption.AllDirectories).Single())!;

    internal AffectedExecutionFixture(bool unknown = false)
    {
        var repository = TestRepositoryLayout.FindRoot();
        Write(".gitignore", "build/\n.lake/\n**/bin/\n**/obj/\nlocal-runtime/\n");
        Write("NuGet.Config", "<configuration><packageSources><clear /></packageSources></configuration>\n");
        Write("global.json", File.ReadAllText(Path.Combine(repository, "global.json")));
        Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"1111111111111111111111111111111111111111\"}]}\n");
        Write("README.md", "a\n");
        Write("Meta/FILEMAP.toml", File.ReadAllText(Path.Combine(repository, "Meta/FILEMAP.toml")).Split("[[test_input_owners]]")[0] + Owner(First) + Owner(Second));
        Write("tools/scripts/ci-build-outputs.targets", File.ReadAllText(Path.Combine(repository, "tools/scripts/ci-build-outputs.targets")));
        Write("tools/scripts/report/dotnet_producer.py", File.ReadAllText(Path.Combine(repository, "tools/scripts/report/dotnet_producer.py")));
        foreach (var (name, assembly) in new[] { ("StrataLint.Cli", "StrataLint"),
                     ("StrataLint.EngineeringScope", "StrataLint.EngineeringScope"), ("StrataLint.Scribe.Documents", "StrataLint.Scribe.Documents"),
                     ("StrataLint.Lean", "StrataLint.Lean") })
        {
            Write($"tools/{name}/{name}.csproj", $"""
                <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
                <AssemblyName>{assembly}</AssemblyName><GenerateRuntimeConfigurationFiles>true</GenerateRuntimeConfigurationFiles>
                <RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup></Project>
                """);
            Write($"tools/{name}/Value.cs", "public class Host { }\n");
        }
        Write("tools/StrataLint.Shared/StrataLint.Shared.csproj", "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><TargetFramework>net10.0</TargetFramework><RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup></Project>\n");
        Write("tools/StrataLint.Shared/Value.cs", "public static class Shared { public static int Value() => 7; }\n");
        foreach (var project in new[] { First, Second })
            Write(project, """
                <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
                <IsTestProject>true</IsTestProject><RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup>
                <ItemGroup><PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" />
                <PackageReference Include="xunit" Version="2.9.3" /><PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" />
                <ProjectReference Include="../../StrataLint.Shared/StrataLint.Shared.csproj" /></ItemGroup></Project>
                """);
        Write("tools/tests/StrataLint.First/Tests.cs", "namespace First; public class Tests { [Xunit.Fact] public void Runs() { Xunit.Assert.Equal(7, Shared.Value()); } }\n");
        if (unknown) Write("local-runtime/value.txt", "7");
        Write("tools/tests/StrataLint.Second/Tests.cs", "namespace Second; public class Tests { [Xunit.Fact] public void Runs() { Xunit.Assert.Equal(7, Shared.Value()); } }\n"
            + (unknown ? "public class Ambient { [Xunit.Fact] public void Runs() { Xunit.Assert.NotNull(System.Environment.GetEnvironmentVariable(\"PATH\")); "
                + "Xunit.Assert.Equal(\"7\", System.IO.File.ReadAllText(" + JsonSerializer.Serialize(Path.Combine(Root, "local-runtime/value.txt")) + ")); } } public class Additional { [Xunit.Fact] public void Known() { Xunit.Assert.Equal(7, Shared.Value()); } }\n" : ""));
        Run("git", "init", "-q");
        Run("dotnet", "new", "sln", "--name", "StrataLint", "--format", "sln", "--output", "tools");
        Run("dotnet", "sln", "tools/StrataLint.sln", "add", First, Second,
            "tools/StrataLint.Cli/StrataLint.Cli.csproj", "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj",
            "tools/StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj", "tools/StrataLint.Lean/StrataLint.Lean.csproj");
        Run("dotnet", "restore", "tools/StrataLint.sln", "--use-lock-file");
        Run("git", "add", ".");
        Run("git", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "parentless");
    }

    internal static string Owner(string project) => $$"""

        [[test_input_owners]]
        project = "{{project}}"
        contract = "ExplicitValues"
        version = 1
        producer = "StrataLint.Engine.ScribeExecutionDependencies.Derive"
        verifier = "StrataLint.EngineeringScope.AffectedTestCache.ValidateSource"
        runner = "StrataLint.EngineeringScope.Program.RunTests"
        runner_contract = "StandardXunitInline-v1"

        """;

    internal void UnenrollFirst() => Write("Meta/FILEMAP.toml",
        File.ReadAllText(Path.Combine(Root, "Meta/FILEMAP.toml")).Replace(Owner(First), "", StringComparison.Ordinal));

    internal CommonStageRecord Build()
    {
        using var deadline = new CancellationTokenSource(TestBudgets.WorkflowProcessHangGuard);
        var root = SharedBuildContractTests.Git(Root, "rev-parse", "--show-toplevel");
        Assert.True(new CommonStages(root, Output, deadline.Token).Run("build", null) == 0, Output.ToString());
        var record = CommonExecutionEvidence.ValidateBuild(Root);
        Retain("build-" + ++buildNumber);
        return record;
    }

    internal TestExecutionRecord Tests(CommonStageRecord build, int? expectedExit = 0, bool subprocess = false)
    {
        string[] arguments = ["--repository", Root, "--all", "--build-round", build.Round];
        int exit;
        if (subprocess)
        {
            using var deadline = new CancellationTokenSource(TestBudgets.WorkflowProcessHangGuard);
            var result = new CommonStages(Root, Output, deadline.Token).Capture("dotnet", [typeof(Program).Assembly.Location, .. arguments]);
            Output.WriteLine(result.Text);
            exit = result.Exit;
        }
        else exit = Program.Run(arguments, TestResultEvidence.Load, Output, Output);
        Output.WriteLine($"FIXTURE_TEST_EXIT invocation={testNumber + 1} subprocess={subprocess} exit={exit}");
        Retain("tests-" + ++testNumber);
        if (expectedExit is not null) Assert.True(exit == expectedExit, Output.ToString());
        return CommonExecutionEvidence.Read<TestExecutionRecord>(Root, CommonExecutionEvidence.TestsPath);
    }

    internal void Remove(string path) => TemporaryFileSystem.File.Delete(Path.Combine(Root, path));
    internal void VerifyTestHostCultures(string culture, string uiCulture)
    {
        const string project = "local-runtime/culture-probe/CultureProbe.csproj";
        Write(project, """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
            <IsTestProject>true</IsTestProject></PropertyGroup><ItemGroup>
            <PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" />
            <PackageReference Include="xunit" Version="2.9.3" />
            <PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" />
            </ItemGroup></Project>
            """);
        Write("local-runtime/culture-probe/Cultures.cs", $$"""
            public class Cultures
            {
                [Xunit.Fact] public void LaunchedTestHostUsesChildContext()
                {
                    var culture = System.Globalization.CultureInfo.CurrentCulture.Name;
                    var uiCulture = System.Globalization.CultureInfo.CurrentUICulture.Name;
                    System.Console.WriteLine("TESTHOST_CULTURES " + System.Text.Json.JsonSerializer.Serialize(new {
                        culture, uiCulture, language = System.Environment.GetEnvironmentVariable("DOTNET_CLI_UI_LANGUAGE") }));
                    Xunit.Assert.Equal({{JsonSerializer.Serialize(culture)}}, culture);
                    Xunit.Assert.Equal({{JsonSerializer.Serialize(uiCulture)}}, uiCulture);
                    Xunit.Assert.Equal("en-US", System.Environment.GetEnvironmentVariable("DOTNET_CLI_UI_LANGUAGE"));
                }
            }
            """);
        using var deadline = new CancellationTokenSource(TestBudgets.WorkflowProcessHangGuard);
        var result = new CommonStages(Root, Output, deadline.Token).Capture("dotnet",
            ["test", project, "--configuration", "Release", "--logger", "trx;LogFileName=cultures.trx",
                "--results-directory", Path.Combine(Root, "build/ci/culture-probe")]);
        Output.WriteLine(result.Text);
        Retain("culture-probe");
        Assert.True(result.Exit == 0, result.Text);
    }
    internal TestInputManifest Plan() => CommonExecutionEvidence.Read<TestInputManifest>(Root, AffectedTestPlan.PathName);
    internal void ClearSeed() => TemporaryFileSystem.Directory.Delete(Path.Combine(Root, AffectedTestCache.CachePath), recursive: true);
    internal void Transport(string command, params string[] options)
    {
        var script = Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean_actions.py");
        var start = new System.Diagnostics.ProcessStartInfo("python3") { WorkingDirectory = Root,
            UseShellExecute = false, RedirectStandardOutput = true, RedirectStandardError = true };
        foreach (var argument in new[] { script, command, "--repository", Root, "--layers", "tests" }.Concat(options)) start.ArgumentList.Add(argument);
        foreach (var (key, value) in new[] { ("GITHUB_RUN_ID", "17"), ("GITHUB_RUN_ATTEMPT", "2"),
                     ("GITHUB_EVENT_NAME", "push"), ("GITHUB_REF", "refs/heads/dev"), ("STRATALINT_CACHE_WRITES", "true"),
                     ("STRATALINT_CHECK_SUCCEEDED", "true"), ("GITHUB_OUTPUT", ""), ("GITHUB_ENV", "") }) start.Environment[key] = value;
        using var process = System.Diagnostics.Process.Start(start)!;
        var stdout = process.StandardOutput.ReadToEnd(); var stderr = process.StandardError.ReadToEnd();
        Assert.True(process.WaitForExit((int)TestBudgets.WorkflowProcessHangGuard.TotalMilliseconds));
        Output.WriteLine(stdout + stderr);
        Assert.Equal(0, process.ExitCode);
    }
    internal string TransportKey()
    {
        using var manifest = JsonDocument.Parse(File.ReadAllText(Path.Combine(Root, "build/lean-cache/tests/manifest.json")));
        return manifest.RootElement.GetProperty("key").GetString()!;
    }
    internal JsonDocument Coverage() => JsonDocument.Parse(File.ReadAllText(Path.Combine(Root, CommonExecutionEvidence.TestsPath)));
    internal void Write(string path, string text)
    {
        var full = Path.Combine(Root, path);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(full)!);
        TemporaryFileSystem.File.WriteAllText(full, text);
    }
    internal void Run(string executable, params string[] arguments)
    {
        var result = SharedBuildContractTests.Process(Root, executable, arguments);
        Assert.True(result.Exit == 0, result.Text);
    }
    private void Retain(string name)
    {
        // The owning test opts in before cleanup; raw TRX bytes are never rewritten.
        var destination = Environment.GetEnvironmentVariable("AFFECTED_EVIDENCE_ROOT");
        if (string.IsNullOrEmpty(destination)) return;
        var target = Path.Combine(destination, Path.GetFileName(Root), name);
        Directory.CreateDirectory(target);
        foreach (var path in Directory.EnumerateFiles(Path.Combine(Root, "build/ci"), "*", SearchOption.AllDirectories)
                     .Where(path => path.EndsWith(".trx", StringComparison.Ordinal) || path.EndsWith(".json", StringComparison.Ordinal) || path.EndsWith(".log", StringComparison.Ordinal)))
        {
            if (path.Contains("/packages/", StringComparison.Ordinal)) continue;
            var file = Path.Combine(target, Path.GetRelativePath(Path.Combine(Root, "build/ci"), path));
            Directory.CreateDirectory(Path.GetDirectoryName(file)!);
            File.Copy(path, file, overwrite: true);
        }
        var cache = Environment.GetEnvironmentVariable("STRATALINT_TEST_CACHE_ROOT") ?? Path.Combine(Root, AffectedTestCache.CachePath);
        if (Directory.Exists(cache))
        {
            var files = Directory.GetFiles(cache, "*", SearchOption.AllDirectories);
            File.WriteAllText(Path.Combine(target, "cache-inventory.json"), JsonSerializer.Serialize(new {
                bytes = files.Sum(file => new FileInfo(file).Length), files = files.Select(file => Path.GetRelativePath(cache, file)).Order(StringComparer.Ordinal) }));
            foreach (var seed in files.Where(file => Path.GetFileName(file) is "seed.json" or "seed.json.sha256"))
                File.Copy(seed, Path.Combine(target, "success-" + Path.GetFileName(seed)), overwrite: true);
        }
        var transport = Path.Combine(Root, "build/lean-cache/tests/manifest.json");
        if (File.Exists(transport)) File.Copy(transport, Path.Combine(target, "cache-transport.json"), overwrite: true);
        File.WriteAllText(Path.Combine(target, "runner.log"), Output.ToString());
    }
    public void Dispose() { Output.Dispose(); TemporaryFileSystem.Directory.Delete(Root, recursive: true); }
}
