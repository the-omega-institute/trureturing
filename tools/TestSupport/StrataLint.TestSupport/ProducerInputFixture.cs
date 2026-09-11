using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using Xunit;

namespace StrataLint.TestSupport;

internal sealed class ProducerInputFixture : IDisposable
{
    internal const string FetcherPath = "tools/scripts/worktree/lean-cache-publish.sh";
    internal const string CliProjectPath = "tools/StrataLint.Cli/StrataLint.Cli.csproj";
    internal const string LeanRegistrationPath = "Meta/ReportProducers/lean-report.json";
    internal const string ScribeRegistrationPath = "Meta/ReportProducers/scribe-content.json";
    internal const string UnavailableSdk =
        "{\"sdk\":{\"version\":\"99.0.100\",\"rollForward\":\"disable\"}}\n";
    private const string InputHelperPath = "tools/scripts/report/lean-report-input.sh";
    private const string Revision = "0123456789abcdef0123456789abcdef01234567";
    private static readonly string[] Scripts =
    [
        "tools/lean-inspector/inspect.sh", "tools/lean-inspector/Inspector.lean",
        "tools/lean-inspector/delta.py", "tools/lean-inspector/materials.py",
        "tools/lean-inspector/report_cache.py", "tools/lean-inspector/runtime_identity.py",
        InputHelperPath, "tools/scripts/report/producer_paths.py", "tools/scripts/report/dotnet_producer.py",
        "tools/scripts/lean-report-pair.sh", FetcherPath,
        "tools/scripts/worktree/lean-cache-input.sh", "tools/scripts/worktree/lean_cache.py",
    ];
    private readonly TemporaryDirectory temporary = new();
    private readonly string repository;
    private readonly string physicalRepository;
    private readonly Dictionary<string, string> properties = new(StringComparer.Ordinal)
    {
        ["NETCoreSdkVersion"] = "fixture-sdk",
        ["TargetFramework"] = "net10.0",
        ["RuntimeIdentifier"] = "",
        ["DefineConstants"] = "REPORT_FIXTURE",
        ["LangVersion"] = "latest",
        ["Nullable"] = "enable",
        ["ImplicitUsings"] = "enable",
        ["Optimize"] = "true",
        ["AllowUnsafeBlocks"] = "false",
        ["CheckForOverflowUnderflow"] = "false",
        ["PlatformTarget"] = "AnyCPU",
        ["RestorePackagesWithLockFile"] = "false",
        ["NuGetLockFilePath"] = "",
    };

    internal ProducerInputFixture()
    {
        repository = Path.Combine(temporary.Path, "repository");
        ScriptHarnessScratch.EnsureDirectory(repository);
        var physical = TestProcessRunner.Run("pwd", ["-P"], repository,
            TestBudgets.ScriptProcessHangGuard, 4096);
        Assert.Equal(0, physical.ExitCode);
        // Fixture IO retains the temporary root's spelling; producer identities use the physical path.
        physicalRepository = Encoding.UTF8.GetString(physical.StandardOutput).Trim();
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(TestRepositoryLayout.FindRoot(), InputHelperPath), Path.Combine(repository, InputHelperPath));
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/report/producer_paths.py"),
            Path.Combine(repository, "tools/scripts/report/producer_paths.py"));
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/report/dotnet_producer.py"),
            Path.Combine(repository, "tools/scripts/report/dotnet_producer.py"));
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean-cache-input.sh"),
            Path.Combine(repository, "tools/scripts/worktree/lean-cache-input.sh"));
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean_cache.py"),
            Path.Combine(repository, "tools/scripts/worktree/lean_cache.py"));
        Write("tools/lean-inspector/inspect.sh",
            "#!/bin/bash\ndotnet run --project \"$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj\" --configuration Release --\n");
        Write("tools/lean-inspector/Inspector.lean", "def inspector := 1\n");
        foreach (var module in new[] { "delta", "materials", "report_cache", "runtime_identity" })
            Write($"tools/lean-inspector/{module}.py", "# synthetic dependency\n");
        Write("tools/scripts/lean-report-pair.sh", "#!/bin/bash\n");
        Write("tools/scripts/workflow/scribe-content-checks.sh", "#!/bin/bash\n");
        Write(FetcherPath, "#!/bin/bash\n");
        Write("global.json", "{}\n");
        var props = new System.Xml.Linq.XDocument(new System.Xml.Linq.XElement("Project",
            new System.Xml.Linq.XElement("PropertyGroup", properties.Select(pair =>
                new System.Xml.Linq.XElement(pair.Key, pair.Value)))));
        Write("producer.props", props.ToString());
        foreach (var project in new[]
                 { "StrataLint.Cli", "StrataLint.Engine", "StrataLint.Scribe", "StrataLint.Scribe.Documents", "Trureturing.Truth" })
        {
            // No SDK imports: this fixture's semantic preimage is fully explicit.
            Write($"tools/{project}/{project}.csproj",
                "<Project><Import Project=\"../../producer.props\" /><ItemGroup>"
                + "<Compile Include=\"Fixture.cs\" /></ItemGroup></Project>\n");
            Write($"tools/{project}/Fixture.cs", "internal class Fixture { }\n");
            Write($"tools/{project}/packages.lock.json", "{}\n");
        }
        Write("Trureturing.lean", "import D5.Probe\n");
        Write("D5/Probe.lean", "def probe := 1\n");
        Write("lean-toolchain", "leanprover/lean4:v4.33.0\n");
        Write("lakefile.toml", "name = \"fixture\"\n");
        Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"" + Revision + "\"}]}\n");
        RegisterScripts();
    }

    internal void RegisterScripts(params string[] additional)
    {
        WriteRegistration(LeanRegistrationPath, Scripts.Concat(additional), [CliProjectPath]);
        WriteRegistration(ScribeRegistrationPath,
            Scripts.Concat(additional).Append("tools/scripts/workflow/scribe-content-checks.sh"),
            [CliProjectPath, "tools/StrataLint.Scribe/StrataLint.Scribe.csproj",
                "tools/StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj",
                "tools/StrataLint.Engine/StrataLint.Engine.csproj", "tools/Trureturing.Truth/Trureturing.Truth.csproj"]);
    }

    internal void WriteRegistration(string path, IEnumerable<string> scripts, IEnumerable<string> projects) =>
        Write(path, JsonSerializer.Serialize(new { schema = "report-producer-scope-v1", scripts, projects }) + "\n");

    internal string CliProject => Path.Combine(physicalRepository, CliProjectPath);

    internal void UsePrebuiltEntrypoint() => Write("tools/lean-inspector/inspect.sh",
        "#!/bin/bash\ndotnet \"$ROOT/tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll\" worktree with-cache-writer --\n");

    internal ProcessOutput Run(string command, string? workingDirectory = null) => TestProcessRunner.Run(
        "/usr/bin/env", ["-u", "PYTHONDONTWRITEBYTECODE", "-u", "PYTHONPYCACHEPREFIX",
            "/bin/bash", Path.Combine(physicalRepository, InputHelperPath), command, "--repository", physicalRepository],
        workingDirectory ?? physicalRepository, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);

    internal string[] ProducerSourceImage() => Directory.EnumerateFiles(
            Path.Combine(repository, "tools"), "*", SearchOption.AllDirectories)
        .Select(path => Path.GetRelativePath(repository, path).Replace('\\', '/'))
        .Order(StringComparer.Ordinal).Select(path => HashFile(path) + "  " + path).ToArray();

    internal string[] Address()
    {
        var result = Run("address");
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        return Encoding.UTF8.GetString(result.StandardOutput).Trim().Split(' ');
    }

    internal ProcessOutput AddressFromForeignSdkDirectory()
    {
        var directory = Path.Combine(temporary.Path, "foreign sdk");
        ScriptHarnessScratch.EnsureDirectory(directory);
        ScriptHarnessScratch.WriteScratchText(Path.Combine(directory, "global.json"), UnavailableSdk);
        return Run("address", directory);
    }

    internal ProcessOutput EvaluateCliProject() => TestProcessRunner.Run("dotnet",
        ["msbuild", CliProject, "-nologo", "-noAutoResponse", "-nodeReuse:false", "-verbosity:quiet",
            "-property:Configuration=Release", "-getItem:Compile"],
        physicalRepository, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);

    internal void Write(string relativePath, string contents)
    {
        var path = Path.Combine(repository, relativePath);
        ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(path)!);
        ScriptHarnessScratch.WriteScratchText(path, contents);
    }

    internal void Append(string path, string contents) =>
        ScriptHarnessScratch.AppendScratchText(Path.Combine(repository, path), contents);

    internal void Remove(string path) => ScriptHarnessScratch.DeleteScratchFile(Path.Combine(repository, path));

    internal void RemoveInspectorRoot() => Directory.Delete(Path.Combine(repository, "tools/lean-inspector"), true);

    internal byte[] ExpectedAddressBytes()
    {
        string[] producerPaths =
        [
            LeanRegistrationPath, CliProjectPath, "tools/StrataLint.Cli/Fixture.cs", "producer.props", "global.json",
            "tools/lean-inspector/inspect.sh", "tools/lean-inspector/Inspector.lean",
            "tools/lean-inspector/delta.py", "tools/lean-inspector/materials.py",
            "tools/lean-inspector/report_cache.py", "tools/lean-inspector/runtime_identity.py",
            InputHelperPath, "tools/scripts/report/producer_paths.py", "tools/scripts/report/dotnet_producer.py",
            "tools/scripts/lean-report-pair.sh", FetcherPath,
            "tools/scripts/worktree/lean-cache-input.sh", "tools/scripts/worktree/lean_cache.py",
        ];
        var semantics = JsonSerializer.Serialize(properties.OrderBy(pair => pair.Key, StringComparer.Ordinal)
            .Select(pair => new[] { CliProjectPath + ":" + pair.Key, pair.Value }));
        var manifest = producerPaths.Select(path => HashFile(path) + "  " + path + "\n")
            .Append(Hash(semantics) + "  @msbuild-semantics\n").Order(StringComparer.Ordinal);
        var producer = Hash(string.Concat(manifest));
        var sources = Hash(string.Concat(new[]
            { "Trureturing.lean", "D5/Probe.lean", "tools/lean-inspector/Inspector.lean" }
            .Select(path => HashFile(path) + "  " + path + "\n")));
        var config = Hash("{\"lean\":{\"libraries\":[]},\"packages\":[{\"name\":\"mathlib\",\"rev\":\"" + Revision
            + "\"}],\"schema\":\"lean-semantic-config-v1\",\"toolchain\":\"leanprover/lean4:v4.33.0\"}\n");
        var address = Hash("schema=stratalint-lean-report-repository-input-v1\n"
            + $"repository_inspector_sha256={producer}\nlean_sources_sha256={sources}\nlean_config_sha256={config}\n");
        return Encoding.UTF8.GetBytes($"{address} {producer} {sources} {config}\n");
    }

    internal static void CopyBatchProducerInputs(string root)
    {
        using var fixture = new ProducerInputFixture();
        foreach (var path in TemporaryFileSystem.Directory.EnumerateFiles(fixture.repository, "*", SearchOption.AllDirectories))
        {
            var relative = Path.GetRelativePath(fixture.repository, path).Replace('\\', '/');
            if (relative.StartsWith("D5/", StringComparison.Ordinal)
                || relative.StartsWith("Blueprint/", StringComparison.Ordinal)
                || relative == "Trureturing.lean") continue;
            var destination = Path.Combine(root, relative);
            if (TemporaryFileSystem.File.Exists(destination)) continue;
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            TemporaryFileSystem.File.WriteAllBytes(destination, TemporaryFileSystem.File.ReadAllBytes(path));
        }
        TemporaryFileSystem.File.WriteAllBytes(Path.Combine(root, InputHelperPath),
            TemporaryFileSystem.File.ReadAllBytes(Path.Combine(fixture.repository, InputHelperPath)));
    }

    internal static void AttestBatchReport(string root, string report)
    {
        var result = TestProcessRunner.Run("/bin/bash",
            [Path.Combine(root, InputHelperPath), "address", "--repository", root], root,
            TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        var fields = Encoding.UTF8.GetString(result.StandardOutput).Trim().Split(' ');
        var hash = Convert.ToHexStringLower(SHA256.HashData(TemporaryFileSystem.File.ReadAllBytes(report)));
        TemporaryFileSystem.File.WriteAllText(report + ".sha256", $"{hash}  {Path.GetFileName(report)}\n");
        TemporaryFileSystem.File.WriteAllText(report + ".provenance.json", "{}\n");
        TemporaryFileSystem.File.WriteAllText(report + ".input.attestation",
            "schema=stratalint-lean-report-input-attestation-v1\n"
            + $"repository_input_sha256={fields[0]}\nproducer_sha256={fields[1]}\nreport_sha256={hash}\n");
    }

    private string HashFile(string path) =>
        Convert.ToHexStringLower(SHA256.HashData(
            ScriptHarnessScratch.ReadScratchBytes(temporary, Path.Combine("repository", path))));

    private static string Hash(string value) => Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(value)));

    public void Dispose() => temporary.Dispose();
}
