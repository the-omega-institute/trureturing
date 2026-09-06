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
    [InlineData(false)]
    [InlineData(true)]
    public void InspectorRejectsProducerClosureFailureWithoutPublishingReport(bool injectedDotnetFailure)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var repository = CreateRepository(temporary.Path);
        if (!injectedDotnetFailure)
            File.AppendAllText(Path.Combine(repository, "tools", "StrataLint.Cli", "StrataLint.Cli.csproj"), "<");
        var bin = Path.Combine(temporary.Path, "bin");
        Directory.CreateDirectory(bin);
        var dotnet = Path.Combine(bin, "dotnet");
        File.WriteAllText(dotnet, "#!/usr/bin/env bash\nexit 71\n");
        File.SetUnixFileMode(dotnet, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = RunInspector(temporary.Path, repository, injectedDotnetFailure ? bin : "");

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("producer closure is unavailable", Encoding.UTF8.GetString(result.StandardError));
        AssertNoReport(temporary.Path, result);
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
            "#!/usr/bin/env bash\nif [[ $1 == modules ]]; then printf 'Trureturing\\tTrureturing.lean\\n'; "
            + $"else printf '%s\\n' '{output}'; fi\n");

        var result = RunInspector(temporary.Path, repository, "");

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("malformed", Encoding.UTF8.GetString(result.StandardError));
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
            { InspectorScript, InspectorSource, MaterialCompactor, InputScript, ResourceObservationLibrary })
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
        foreach (var project in new[] { "StrataLint.Cli", "StrataLint.Engine", "Trureturing.Truth" })
        {
            Write(repository, $"tools/{project}/{project}.csproj", "<Project Sdk=\"Microsoft.NET.Sdk\" />\n");
            Write(repository, $"tools/{project}/Fixture.cs", "// fixture\n");
        }
        Write(repository, "tools/scripts/lean-report-pair.sh", "#!/usr/bin/env bash\n");
        Write(repository, "tools/scripts/workflow/scribe-content-checks.sh", "#!/usr/bin/env bash\n");
        Write(repository, ".github/workflows/ci.yml",
            "jobs:\n  lean-inspect:\n    steps: []\n  baseline-admission:\n    steps: []\n");
        Write(repository, "lean-toolchain", "leanprover/lean4:v4.31.0\n");
        Write(repository, "lakefile.toml", "name = \"Fixture\"\n");
        Write(repository, "lake-manifest.json", "{\"version\":\"1.1.0\"}\n");
        LeanReportProducerFixture.SeedReachableScripts(repository);
    }

    private static ProcessOutput RunInspector(string temporary, string repository, string bin)
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
            "PATH=\"$1:$PATH\" LAKE_BIN=\"$2\" STUB_LOG=\"$3\" exec \"$4\" --repository \"$5\" --output \"$6\"",
            "inspect-failure", bin, lake, Path.Combine(temporary, "lake.log"),
            Path.Combine(repository, InspectorScript), repository, Path.Combine(temporary, "report.json")], repository);
    }

    private static void AssertNoReport(string temporary, ProcessOutput result)
    {
        Assert.DoesNotContain("RAW_LEAN_REPORT", Encoding.UTF8.GetString(result.StandardOutput));
        foreach (var suffix in new[] { "", ".sha256", ".materials.zip" })
            Assert.False(File.Exists(Path.Combine(temporary, "report.json") + suffix));
        Assert.Equal(["build"], File.ReadAllLines(Path.Combine(temporary, "lake.log")));
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
