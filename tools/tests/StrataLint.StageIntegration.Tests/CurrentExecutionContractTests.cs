using StrataLint.EngineeringScope;
using System.Diagnostics;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.StageIntegration.Tests;

public sealed partial class CurrentExecutionContractTests
{
    [Fact]
    public void CompilerOutputIdentityMustMatchProjectRegistration()
    {
        using var fixture = new ExecutionFixture();
        var directory = Path.Combine(fixture.Root, CommonBuildOutputs.RootPath);
        TemporaryFileSystem.Directory.CreateDirectory(directory);
        var assembly = Path.Combine(directory, Path.GetFileName(typeof(CurrentExecutionContractTests).Assembly.Location));
        TemporaryFileSystem.File.WriteAllBytes(assembly, File.ReadAllBytes(typeof(CurrentExecutionContractTests).Assembly.Location));
        var receipt = Path.Combine(directory, ExecutionFixture.First + ".outputs");
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(receipt)!);
        TemporaryFileSystem.File.WriteAllText(receipt,
            string.Join("\n", new[] { Path.Combine(fixture.Root, ExecutionFixture.First), assembly, directory, "packages=" + Path.Combine(fixture.Root, "build/packages"), "reference=", assembly }));

        var failure = Assert.Throws<InvalidDataException>(() => CommonBuildOutputs.Collect(fixture.Root));

        Assert.Contains("compiler assembly identity mismatch", failure.Message, StringComparison.Ordinal);
        Assert.Contains("First", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ParentlessRemotelessCandidateRunsEveryProjectOnceAndRetainsEvidence()
    {
        using var fixture = new ExecutionFixture();
        var calls = new List<string>();
        var exit = Program.RunCurrentTests(fixture.Root, (project, results) =>
        {
            calls.Add(project);
            fixture.WriteTrx(results, "Passed");
            return 0;
        }, TextWriter.Null);
        Assert.Equal(0, exit);
        Assert.Equal(new[] { ExecutionFixture.First, ExecutionFixture.Second }, calls);
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
        using var fixture = new ExecutionFixture();
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
        using var fixture = new ExecutionFixture();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, results) =>
        {
            fixture.WriteTrx(results, "Passed");
            return 0;
        }, TextWriter.Null));
        CommonExecutionEvidence.ValidateTests(fixture.Root, [ExecutionFixture.First]);
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateTests(
            fixture.Root, ["tools/tests/Missing/Missing.csproj"]));
        TemporaryFileSystem.File.AppendAllText(Path.Combine(fixture.Root, ExecutionFixture.First), "\n");
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
    }

    [Theory]
    [InlineData("source", "candidate changed during test execution")]
    [InlineData("source-mode", "candidate changed during test execution")]
    [InlineData("runtime", "artifact integrity mismatch: build/ci/fixture-bin/First.dll")]
    [InlineData("inventory", "artifact integrity mismatch: " + CommonBuildOutputs.TestsPath)]
    public void TestCompletionRereadsSourceAndBuildMaterials(string mutation, string expected)
    {
        if (mutation == "source-mode" && OperatingSystem.IsWindows()) return;
        using var fixture = new ExecutionFixture();
        var calls = 0;
        var error = Assert.Throws<InvalidDataException>(() => Program.RunCurrentTests(fixture.Root, (_, results) =>
        {
            fixture.WriteTrx(results, "Passed");
            if (++calls == 1)
            {
                var path = Path.Combine(fixture.Root, mutation switch
                {
                    "runtime" => "build/ci/fixture-bin/First.dll",
                    "inventory" => CommonBuildOutputs.TestsPath,
                    _ => ExecutionFixture.First,
                });
                if (mutation == "source-mode" && !OperatingSystem.IsWindows()) File.SetUnixFileMode(path, File.GetUnixFileMode(path) | UnixFileMode.UserExecute);
                else TemporaryFileSystem.File.AppendAllText(path, "\n");
            }
            return 0;
        }, TextWriter.Null));

        Assert.Equal(2, calls);
        Assert.Equal(expected, error.Message);
    }

    [Fact]
    public void TestCompletionRecomputesDeclaredExecutionEnvironment()
    {
        using var fixture = new ExecutionFixture();
        const string name = "CONTRACT_TEST_COMPLETION_ENVIRONMENT";
        var original = Environment.GetEnvironmentVariable(name);
        try
        {
            EditRegistration(fixture, projects => projects[0]!["execution_environment"] = new System.Text.Json.Nodes.JsonArray(name));
            Environment.SetEnvironmentVariable(name, "before");
            fixture.Build();
            using var output = new StringWriter();
            var calls = 0;
            var exit = Program.RunCurrentTests(fixture.Root, (_, results) =>
            {
                ++calls;
                fixture.WriteTrx(results, "Passed");
                Environment.SetEnvironmentVariable(name, "after");
                return 0;
            }, output);

            Assert.Equal(2, calls);
            Assert.Equal(1, exit);
            Assert.Contains("test input identity mismatch: " + ExecutionFixture.First, output.ToString(), StringComparison.Ordinal);
        }
        finally { Environment.SetEnvironmentVariable(name, original); }
    }

    [Fact]
    public void EvidenceSurvivesTransportToIdenticalCheckout()
    {
        using var fixture = new ExecutionFixture();
        using var target = new ExecutionFixture();
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
        using var fixture = new ExecutionFixture();
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

    [Theory]
    [InlineData("passed")]
    [InlineData("failed")]
    [InlineData("exception")]
    public async Task ConcurrentProjectsOverlapAndJoinBeforeEvidenceIsAccepted(string outcome)
    {
        using var fixture = new ExecutionFixture();
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var starts = 0;
        using var release = new ManualResetEventSlim();
        var calls = new System.Collections.Concurrent.ConcurrentBag<string>();
        using var output = new StringWriter();
        var work = Task.Run(() => Program.RunCurrentTests(fixture.Root, (project, results) =>
        {
            calls.Add(project);
            if (Interlocked.Increment(ref starts) == 2) entered.SetResult();
            // This deadline only releases a broken scheduler; elapsed time is not the assertion.
            if (!release.Wait(TestBudgets.PlaybookProcessHangGuard)) throw new TimeoutException("concurrent runner hang guard");
            if (project == ExecutionFixture.First && outcome == "exception") throw new IOException("fixture execution error");
            var failed = project == ExecutionFixture.First && outcome == "failed";
            fixture.WriteTrx(results, failed ? "Failed" : "Passed");
            return failed ? 1 : 0;
        }, output, maxConcurrentProjects: 2));
        var exit = -1;
        try
        {
            await entered.Task.WaitAsync(TestBudgets.PlaybookProcessHangGuard);
            Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.TestsPath)));
        }
        finally
        {
            release.Set();
            exit = await work.WaitAsync(TestBudgets.PlaybookProcessHangGuard);
        }
        Assert.Equal(outcome == "passed" ? 0 : 1, exit);
        Assert.Equal(new[] { ExecutionFixture.First, ExecutionFixture.Second }, calls.Order(StringComparer.Ordinal));
        var record = CommonExecutionEvidence.Read<TestExecutionRecord>(fixture.Root, CommonExecutionEvidence.TestsPath);
        Assert.Equal(new[] { ExecutionFixture.First, ExecutionFixture.Second }, record.Projects.Select(project => project.Project));
        Assert.Equal(2, record.Projects.Select(project => project.Results).Distinct().Count());
        Assert.All(record.Projects, project => Assert.Equal("executed", project.Status));
        if (outcome == "passed") CommonExecutionEvidence.ValidateTests(fixture.Root);
        else Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
    }

}
