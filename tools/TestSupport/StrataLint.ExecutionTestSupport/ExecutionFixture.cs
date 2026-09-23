using System.Diagnostics;
using System.IO.Compression;
using StrataLint.EngineeringScope;
using Xunit;

namespace StrataLint.TestSupport;

internal sealed class ExecutionFixture : IDisposable
{
    internal const string First = "tools/tests/First/First.csproj";
    internal const string Second = "tools/tests/Second/Second.csproj";
    internal string Root { get; } = TemporaryFileSystem.Directory.CreateTempSubdirectory("current-contract-").FullName;

    internal ExecutionFixture()
    {
        foreach (var path in new[] { First, Second })
        {
            var file = Path.Combine(Root, path);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(file)!);
            TemporaryFileSystem.File.WriteAllText(file, "<Project><PropertyGroup><IsTestProject>true</IsTestProject></PropertyGroup></Project>\n");
        }
        TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(Root, "Meta"));
        TemporaryFileSystem.File.WriteAllText(Path.Combine(Root, EngineeringRegistrationFixture.Path),
            EngineeringRegistrationFixture.Manifest(
                new EngineeringProjectFixture(First, "First", "cross-cutting-test", true, ["tools/tests/First/**/*.cs"]),
                new EngineeringProjectFixture(Second, "Second", "cross-cutting-test", true, ["tools/tests/Second/**/*.cs"])));
        TemporaryFileSystem.File.WriteAllText(Path.Combine(Root, ".gitignore"), ".lake/\nbuild/\nbin/\nobj/\n");
        Write("global.json", "{\"sdk\":{\"version\":\"10.0.103\"}}");
        Write("Meta/ci-checks.json", CommonCheckRegistrationFixture.Manifest(First));
        RegisterProofs();
        Write("tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs", "// banned-api-proof\n");
        Git("init", "-q");
        Git("add", ".");
        Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "parentless");
        Build();
    }

    internal void Write(string path, string text)
    {
        var full = Path.Combine(Root, path);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(full)!);
        TemporaryFileSystem.File.WriteAllText(full, text);
    }

    internal void Track() => Git("add", ".");

    internal CommonStageRecord Build()
    {
        const string log = "build/ci/fixture-build.log";
        Write(log, "built\n");
        var registration = System.Text.Json.Nodes.JsonNode.Parse(TemporaryFileSystem.File.ReadAllText(
            Path.Combine(Root, EngineeringRegistrationFixture.Path)))!;
        var tests = registration["projects"]!.AsArray().Where(row => row!["ci"]!.GetValue<bool>()).Select(row =>
            new BuiltTestProject(row!["path"]!.ToString(), "build/ci/fixture-bin/" + row["assembly"] + ".dll")).ToArray();
        foreach (var test in tests) Write(test.Assembly, "synthetic assembly\n");
        CommonExecutionEvidence.Write(Root, CommonExecutionEvidence.BuildTestsPath, tests);
        return CommonExecutionEvidence.SealBuild(Root, CommonExecutionEvidence.Candidate(Root),
            tests.Select(test => test.Assembly).Append(CommonExecutionEvidence.BuildTestsPath).Append(log),
            CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", log)).ToArray());
    }

    internal void RegisterProofs()
    {
        var path = Path.Combine(Root, EngineeringRegistrationFixture.Path);
        var manifest = TemporaryFileSystem.File.ReadAllText(path);
        foreach (var name in new[] { "CompileFailProof", "BannedApiCompileFailProof" })
        {
            var project = $"tools/tests/{name}/{name}.csproj";
            if (System.Text.Json.Nodes.JsonNode.Parse(manifest)!["projects"]!.AsArray().Any(row => row!["path"]!.ToString() == project)) continue;
            var full = Path.Combine(Root, project);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(full)!);
            TemporaryFileSystem.File.WriteAllText(full, "<Project />\n");
            manifest = EngineeringRegistrationFixture.Append(manifest,
                new EngineeringProjectFixture(project, name, "compile-fail-proof", false, [$"tools/tests/{name}/**/*.cs"]));
        }
        TemporaryFileSystem.File.WriteAllText(path, manifest);
    }

    internal void WriteTrx(string directory, string outcome)
    {
        TemporaryFileSystem.Directory.CreateDirectory(directory);
        var executed = outcome == "NotExecuted" ? 0 : 1;
        var assembly = Path.GetFileName(directory) == "1" ? "Second" : "First";
        TemporaryFileSystem.File.WriteAllText(Path.Combine(directory, "execution.trx"), $"""
            <TestRun><Results><UnitTestResult testId="one" testName="Fixture.Runs" outcome="{outcome}" /></Results>
            <TestDefinitions><UnitTest id="one" storage="{assembly}.dll"><TestMethod className="Fixture" name="Runs" /></UnitTest></TestDefinitions>
            <ResultSummary outcome="{(outcome == "Failed" ? "Failed" : "Completed")}"><Counters executed="{executed}" passed="{(outcome == "Passed" ? 1 : 0)}" failed="{(outcome == "Failed" ? 1 : 0)}" /></ResultSummary></TestRun>
            """);
    }

    private void Git(params string[] arguments)
    {
        var start = new ProcessStartInfo("git") { WorkingDirectory = Root, RedirectStandardOutput = true, RedirectStandardError = true };
        foreach (var argument in arguments) start.ArgumentList.Add(argument);
        using var process = Process.Start(start)!;
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        Assert.True(process.ExitCode == 0, error);
    }

    public void Dispose() => TemporaryFileSystem.Directory.Delete(Root, recursive: true);

    internal static void Report(string root)
    {
        var report = Path.Combine(root, CommonExecutionEvidence.ReportPath);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(report)!);
        TemporaryFileSystem.File.WriteAllText(report, "{\"modules\": [], \"schema\": \"stratalint-raw-lean-report-v2\"}\n");
        using (var stream = File.Create(report + ".materials.zip"))
        using (new ZipArchive(stream, ZipArchiveMode.Create)) { }
        TemporaryFileSystem.File.WriteAllText(report + ".sha256", CommonExecutionEvidence.Hash(report) + "  " + Path.GetFileName(report) + "\n");
        foreach (var suffix in new[] { ".input.attestation", ".provenance.json" })
            TemporaryFileSystem.File.WriteAllText(report + suffix, "fixture companion\n");
    }
}
