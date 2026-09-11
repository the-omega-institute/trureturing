using System.Diagnostics;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class CurrentExecutionContractTests
{
    [Fact]
    public void CompilerOutputIdentityMustMatchProjectRegistration()
    {
        using var fixture = new CandidateFixture();
        var directory = Path.Combine(fixture.Root, CommonBuildOutputs.RootPath);
        TemporaryFileSystem.Directory.CreateDirectory(directory);
        var assembly = Path.Combine(directory, Path.GetFileName(typeof(CurrentExecutionContractTests).Assembly.Location));
        TemporaryFileSystem.File.WriteAllBytes(assembly, File.ReadAllBytes(typeof(CurrentExecutionContractTests).Assembly.Location));
        TemporaryFileSystem.File.WriteAllText(Path.Combine(directory, "fixture.outputs"),
            string.Join("\n", new[] { Path.Combine(fixture.Root, CandidateFixture.First), assembly, directory, "unused-assets.json", "reference=", assembly }));

        var failure = Assert.Throws<InvalidDataException>(() => CommonBuildOutputs.Collect(fixture.Root));

        Assert.Contains("compiler assembly identity mismatch", failure.Message, StringComparison.Ordinal);
        Assert.Contains("First", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ParentlessRemotelessCandidateRunsEveryProjectOnceAndRetainsEvidence()
    {
        using var fixture = new CandidateFixture();
        var calls = new List<string>();
        var exit = Program.RunCurrentTests(fixture.Root, (project, results) =>
        {
            calls.Add(project);
            fixture.WriteTrx(results, "Passed");
            return 0;
        }, TextWriter.Null);
        Assert.Equal(0, exit);
        Assert.Equal(new[] { CandidateFixture.First, CandidateFixture.Second }, calls);
        Assert.True(TemporaryFileSystem.File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.TestsPath)));
        Assert.Equal(2, TemporaryFileSystem.Directory.EnumerateFiles(
            Path.Combine(fixture.Root, CommonExecutionEvidence.RootPath), "*.trx", SearchOption.AllDirectories).Count());
        CommonExecutionEvidence.ValidateTests(fixture.Root);
    }

    [Theory]
    [InlineData("Failed", 0)]
    [InlineData("Passed", 19)]
    [InlineData("NotExecuted", 0)]
    public void FailedOrEmptyExecutionCannotProduceSuccessfulEvidence(string outcome, int processExit)
    {
        using var fixture = new CandidateFixture();
        var exit = Program.RunCurrentTests(fixture.Root, (_, results) =>
        {
            fixture.WriteTrx(results, outcome);
            return processExit;
        }, TextWriter.Null);
        Assert.NotEqual(0, exit);
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
    }

    [Fact]
    public void EvidenceRejectsCandidateMutationAndMissingBaseProject()
    {
        using var fixture = new CandidateFixture();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, results) =>
        {
            fixture.WriteTrx(results, "Passed");
            return 0;
        }, TextWriter.Null));
        CommonExecutionEvidence.ValidateTests(fixture.Root, [CandidateFixture.First]);
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateTests(
            fixture.Root, ["tools/tests/Missing/Missing.csproj"]));
        TemporaryFileSystem.File.AppendAllText(Path.Combine(fixture.Root, CandidateFixture.First), "\n");
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
    }

    [Fact]
    public void EvidenceSurvivesTransportToIdenticalCheckout()
    {
        using var fixture = new CandidateFixture();
        using var target = new CandidateFixture();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, results) =>
        {
            fixture.WriteTrx(results, "Passed");
            return 0;
        }, TextWriter.Null));
        var source = Path.Combine(fixture.Root, CommonExecutionEvidence.RootPath);
        foreach (var file in TemporaryFileSystem.Directory.EnumerateFiles(source, "*", SearchOption.AllDirectories))
        {
            var destination = Path.Combine(target.Root, CommonExecutionEvidence.RootPath, Path.GetRelativePath(source, file));
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            TemporaryFileSystem.File.WriteAllBytes(destination, TemporaryFileSystem.File.ReadAllBytes(file));
        }
        CommonExecutionEvidence.ValidateTests(target.Root);
    }

    [Fact]
    public void FailedRunSummaryCannotHideBehindPassedIndividualResults()
    {
        using var fixture = new CandidateFixture();
        var exit = Program.RunCurrentTests(fixture.Root, (_, directory) =>
        {
            fixture.WriteTrx(directory, "Passed");
            var path = Path.Combine(directory, "execution.trx");
            TemporaryFileSystem.File.WriteAllText(path, TemporaryFileSystem.File.ReadAllText(path).Replace(
                "ResultSummary outcome=\"Completed\"", "ResultSummary outcome=\"Failed\"", StringComparison.Ordinal));
            return 0;
        }, TextWriter.Null);
        Assert.Equal(1, exit);
    }

    internal sealed class CandidateFixture : IDisposable
    {
        internal const string First = "tools/tests/First/First.csproj";
        internal const string Second = "tools/tests/Second/Second.csproj";
        internal string Root { get; } = TemporaryFileSystem.Directory.CreateTempSubdirectory("current-contract-").FullName;

        internal CandidateFixture()
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
            TemporaryFileSystem.File.WriteAllText(Path.Combine(Root, ".gitignore"), ".lake/\nbuild/\n");
            Git("init", "-q");
            Git("add", ".");
            Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "parentless");
        }

        internal void RegisterProofs()
        {
            var path = Path.Combine(Root, EngineeringRegistrationFixture.Path);
            var manifest = System.Text.Json.Nodes.JsonNode.Parse(TemporaryFileSystem.File.ReadAllText(path))!;
            var projects = manifest["projects"]!.AsArray();
            foreach (var name in new[] { "CompileFailProof", "BannedApiCompileFailProof" })
            {
                var project = $"tools/tests/{name}/{name}.csproj";
                var full = Path.Combine(Root, project);
                TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(full)!);
                TemporaryFileSystem.File.WriteAllText(full, "<Project />\n");
                var registration = System.Text.Json.Nodes.JsonNode.Parse(EngineeringRegistrationFixture.Manifest(
                    new EngineeringProjectFixture(project, name, "compile-fail-proof", false, [$"tools/tests/{name}/**/*.cs"])))!;
                projects.Add(registration["projects"]![0]!.DeepClone());
            }
            TemporaryFileSystem.File.WriteAllText(path, manifest.ToJsonString());
        }

        internal void WriteTrx(string directory, string outcome)
        {
            TemporaryFileSystem.Directory.CreateDirectory(directory);
            var executed = outcome == "NotExecuted" ? 0 : 1;
            TemporaryFileSystem.File.WriteAllText(Path.Combine(directory, "execution.trx"), $"""
                <TestRun><Results><UnitTestResult testId="one" testName="Fixture.Runs" outcome="{outcome}" /></Results>
                <TestDefinitions><UnitTest id="one" storage="Fixture.dll"><TestMethod className="Fixture" name="Runs" /></UnitTest></TestDefinitions>
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
    }
}
