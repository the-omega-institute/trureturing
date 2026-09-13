using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean report environment")]
public sealed class LeanInspectorScriptTests
{
    private const string InspectorScript = "tools/lean-inspector/inspect.sh";
    private const string InspectorSource = "tools/lean-inspector/Inspector.lean";
    private const string MaterialCompactor = "tools/lean-inspector/materials.py";
    private const string InputScript = "tools/scripts/report/lean-report-input.sh";
    private const string ResourceObservationLibrary = "tools/scripts/lib/resource-observation-lib.sh";
    private const string CacheRunScript = "tools/scripts/worktree/lean-cache-run.sh";

    [Fact]
    public void InspectorDefaultsToCompleteModuleEnumeration()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var repository = CreateRepository(temporary.Path);
        var lake = Path.Combine(temporary.Path, "lake");
        File.WriteAllText(lake, "#!/usr/bin/env bash\nprintf '%s\\n' \"$*\" >> \"$STUB_LOG\"\nif [[ \"$*\" == *' --output '* ]]; then while [[ $# -gt 0 ]]; do [[ $1 == --output ]] && { printf '{\"modules\": [], \"schema\": \"stratalint-lean-inspector-spool-v1\"}\\n' > \"$2\"; break; }; shift; done; fi\n", new UTF8Encoding(false));
        File.SetUnixFileMode(lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var log = Path.Combine(temporary.Path, "lake.log");
        var output = Path.Combine(temporary.Path, "report.json");

        var full = Run("env", [$"LAKE_BIN={lake}", $"STUB_LOG={log}", Path.Combine(repository, InspectorScript), "--repository", repository, "--output", output], repository);
        Assert.True(full.ExitCode == 0, Encoding.UTF8.GetString(full.StandardError));
        var fullInspect = File.ReadAllLines(log).Single(static line => line.Contains(" --output ", StringComparison.Ordinal));
        Assert.Contains("Trureturing Trureturing.lean sha256:", fullInspect, StringComparison.Ordinal);
        Assert.Contains("D5.Probe D5/Probe.lean sha256:", fullInspect, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false, null)]
    [InlineData(true, null)]
    [InlineData(false, "compatibility_version = 0\n")]
    [InlineData(true, "compatibility_version = \"1\"\n")]
    public void InspectorRejectsInvalidVersionBeforeBuildEvenWithPrecomputedIdentity(bool precomputed, string? version)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var repository = CreateRepository(temporary.Path);
        var manifest = Path.Combine(repository, LeanReportInputScriptTests.CompatibilityPath);
        if (version is null) File.Delete(manifest);
        else File.WriteAllText(manifest, version + LeanReportInputScriptTests.SourcePatterns);

        var result = RunInspector(temporary.Path, repository, "", precomputed);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("compatibility_version", Encoding.UTF8.GetString(result.StandardError));
        AssertNoReport(temporary.Path, result);
        Assert.False(File.Exists(Path.Combine(temporary.Path, "lake.log")), "invalid version reached the build/cache producer");
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("extra")]
    [InlineData("non-hex")]
    [InlineData("multiline")]
    public void InspectorRejectsMalformedAddressBeforeProducingReport(string malformed)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var repository = CreateRepository(temporary.Path);
        var digest = new string('a', 64);
        var output = malformed switch
        {
            "missing" => $"{digest}  {digest} {digest}",
            "extra" => string.Join(' ', Enumerable.Repeat(digest, 5)),
            "non-hex" => $"{digest} {new string('z', 64)} {digest} {digest}",
            "multiline" => string.Join(' ', Enumerable.Repeat(digest, 4)) + "\nextra",
            _ => throw new InvalidOperationException(malformed),
        };
        Write(repository, InputScript,
            $"#!/usr/bin/env bash\nif [[ $1 == compatibility-token ]]; then printf '%s\\n' '{digest}'; "
            + "elif [[ $1 == modules ]]; then printf 'Trureturing\\tTrureturing.lean\\n'; "
            + $"else printf '%s\\n' '{output}'; fi\n");

        var result = RunInspector(temporary.Path, repository, "");

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("repository input address is malformed", Encoding.UTF8.GetString(result.StandardError));
        Assert.False(File.Exists(Path.Combine(temporary.Path, "lake.log")));
        AssertNoReport(temporary.Path, result);
    }

    [Fact]
    public void ProducerDoesNotExecuteCandidateModuleEnumerator()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var repository = Path.Combine(temporary.Path, "repo");
        Directory.CreateDirectory(Path.Combine(repository, "D5"));
        Write(repository, "Trureturing.lean", "import D5.Probe\n");
        Write(repository, "D5/Probe.lean", "def probe : Nat := 1\n");
        var marker = Path.Combine(temporary.Path, "candidate-helper-ran");
        var poisoned = Path.Combine(repository, InputScript);
        Directory.CreateDirectory(Path.GetDirectoryName(poisoned)!);
        File.WriteAllText(
            poisoned,
            $"#!/usr/bin/env bash\ntouch '{marker}'\nprintf 'Trureturing\\tTrureturing.lean\\n'\n",
            new UTF8Encoding(false));
        File.SetUnixFileMode(poisoned, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        InstallCacheRun(repository);
        InstallProducerInputs(repository);
        Assert.Equal(0, Run("git", ["init", "--quiet"], repository).ExitCode);
        var lake = Path.Combine(temporary.Path, "lake");
        File.WriteAllText(lake, "#!/usr/bin/env bash\nif [[ \"$*\" == *' --output '* ]]; then while [[ $# -gt 0 ]]; do [[ $1 == --output ]] && { printf '{\"modules\": [], \"schema\": \"stratalint-lean-inspector-spool-v1\"}\\n' > \"$2\"; break; }; shift; done; fi\n", new UTF8Encoding(false));
        File.SetUnixFileMode(lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = Run("env", [$"LAKE_BIN={lake}", Path.Combine(root, InspectorScript), "--repository", repository, "--output", Path.Combine(temporary.Path, "report.json")], repository);

        Assert.Equal(0, result.ExitCode);
        Assert.False(File.Exists(marker), "producer executed the candidate-owned module enumerator");
    }

    private static ProcessOutput Run(string command, IReadOnlyList<string> arguments, string cwd) =>
        TestProcessRunner.Run(command, arguments, cwd, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);

    private static string CreateRepository(string temporary)
    {
        var repository = Path.Combine(temporary, "repo");
        var root = TestRepositoryLayout.FindRoot();
        Write(repository, "Trureturing.lean", "import D5.Probe\n");
        Write(repository, "D5/Probe.lean", "def probe : Nat := 1\n");
        foreach (var relative in new[]
            { InspectorScript, InspectorSource, MaterialCompactor, InputScript, ResourceObservationLibrary,
                "tools/scripts/worktree/lean-cache-input.sh" })
        {
            Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(repository, relative))!);
            File.Copy(Path.Combine(root, relative), Path.Combine(repository, relative));
        }
        InstallCacheRun(repository);
        InstallProducerInputs(repository);
        return repository;
    }

    private static void InstallProducerInputs(string repository)
    {
        LeanReportInputScriptTests.InstallReportConfiguration(repository);
        foreach (var project in new[] { "StrataLint.Cli", "StrataLint.Engine", "Trureturing.Truth" })
        {
            Write(repository, $"tools/{project}/{project}.csproj", "<Project Sdk=\"Microsoft.NET.Sdk\" />\n");
            Write(repository, $"tools/{project}/Fixture.cs", "// fixture\n");
        }
        Write(repository, "tools/StrataLint.Cli/StrataLint.Cli.csproj",
            "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><OutputType>Exe</OutputType>"
            + "<TargetFramework>net10.0</TargetFramework></PropertyGroup></Project>\n");
        Write(repository, "tools/StrataLint.Cli/Fixture.cs", "System.Console.WriteLine(\"[]\");\n");
        Write(repository, "tools/scripts/lean-report-pair.sh", "#!/usr/bin/env bash\n");
        Write(repository, "tools/scripts/worktree/lean-cache-publish.sh", "#!/usr/bin/env bash\n");
        Write(repository, "tools/scripts/workflow/scribe-content-checks.sh", "#!/usr/bin/env bash\n");
        Write(repository, ".github/workflows/ci.yml",
            "jobs:\n  lean-inspect:\n    steps: []\n  baseline-admission:\n    steps: []\n");
        Write(repository, "lean-toolchain", "leanprover/lean4:v4.31.0\n");
        Write(repository, "lakefile.toml", "name = \"Fixture\"\n");
        Write(repository, "lake-manifest.json", "{\"version\":\"1.1.0\"}\n");
    }

    private static ProcessOutput RunInspector(string temporary, string repository, string bin, bool precomputed = false)
    {
        if (OperatingSystem.IsWindows()) throw new PlatformNotSupportedException();
        var lake = Path.Combine(temporary, "lake");
        File.WriteAllText(lake, """
            #!/usr/bin/env bash
            printf '%s\n' "$*" >> "$STUB_LOG"
            while [[ $# -gt 0 ]]; do
              if [[ "$1" == --output ]]; then
                printf '%s\n' '{"modules":[],"schema":"stratalint-lean-inspector-spool-v1"}' > "$2"
                break
              fi
              shift
            done
            """ + "\n");
        File.SetUnixFileMode(lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        return Run("/bin/bash", ["-c",
            (precomputed ? "export STRATALINT_REPORT_INPUT_ADDRESS=$7 STRATALINT_REPORT_REPOSITORY_SHA256=$7 "
                + "STRATALINT_REPORT_PRODUCER_SHA256=$7 STRATALINT_REPORT_RESIDENT_SHA256=$7 STRATALINT_REPORT_CONFIG_SHA256=$7; " : "")
            + "PATH=\"$1:$PATH\" LAKE_BIN=\"$2\" STUB_LOG=\"$3\" exec \"$4\" --repository \"$5\" --output \"$6\"",
            "inspect-failure", bin, lake, Path.Combine(temporary, "lake.log"),
            Path.Combine(repository, InspectorScript), repository, Path.Combine(temporary, "report.json"), new string('a', 64)], repository);
    }

    private static void AssertNoReport(string temporary, ProcessOutput result)
    {
        Assert.DoesNotContain("RAW_LEAN_REPORT", Encoding.UTF8.GetString(result.StandardOutput));
        foreach (var suffix in new[] { "", ".sha256", ".materials.zip" })
            Assert.False(File.Exists(Path.Combine(temporary, "report.json") + suffix));

    }

    private static void Write(string root, string relative, string contents)
    {
        var path = Path.Combine(root, relative);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, contents, new UTF8Encoding(false));
    }

    private static void InstallCacheRun(string repository)
    {
        if (OperatingSystem.IsWindows()) return;
        Write(repository, CacheRunScript, "#!/usr/bin/env bash\nexec \"$@\"\n");
        File.SetUnixFileMode(
            Path.Combine(repository, CacheRunScript),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }

}
