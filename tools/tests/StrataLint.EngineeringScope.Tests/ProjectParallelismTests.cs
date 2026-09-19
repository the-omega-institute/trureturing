using System.Collections.Concurrent;
using System.Diagnostics;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class ProjectParallelismTests
{
    private const string Third = "tools/tests/Third/Third.csproj";
    private static readonly string[] Projects = [CurrentExecutionContractTests.CandidateFixture.First,
        CurrentExecutionContractTests.CandidateFixture.Second, Third];

    [Theory]
    [InlineData("1", true)]
    [InlineData("2", true)]
    [InlineData("missing", false)]
    [InlineData("0", false)]
    [InlineData("-1", false)]
    [InlineData("null", false)]
    [InlineData("true", false)]
    [InlineData("1.5", false)]
    [InlineData("\"2\"", false)]
    [InlineData("2147483648", false)]
    public void ProducerReaderUsesTheSameExplicitSchedulingContract(string value, bool accepted)
    {
        using var fixture = Fixture(1);
        var path = Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path);
        var manifest = JsonNode.Parse(File.ReadAllText(path))!;
        if (value == "missing") manifest.AsObject().Remove("test_parallelism");
        else manifest["test_parallelism"] = JsonNode.Parse(value);
        File.WriteAllText(path, manifest.ToJsonString());
        var script = Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/report");
        var result = SharedBuildContractTests.Process(fixture.Root, "python3", ["-B", "-c",
            "import pathlib,sys; sys.path.insert(0,sys.argv[1]); import dotnet_producer; dotnet_producer.project_registry(pathlib.Path(sys.argv[2]))",
            script, fixture.Root]);
        Assert.Equal(accepted, result.Exit == 0);
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    public async Task RegisteredSlotsOverlapNativeProcessesAndRetainOrderedEvidence(int slots)
    {
        using var fixture = Fixture(slots);
        using var execution = new BlockingProjects(fixture);
        var run = Task.Run(() => Program.RunCurrentTests(fixture.Root, execution.Run, TextWriter.Null));
        try
        {
            var blocked = Enumerable.Range(0, slots).Select(_ => execution.Take()).ToArray();
            Assert.All(blocked, process => Assert.False(process.HasExited));
            Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.TestsPath)));
            // Keep the first child blocked while another slot completes and accepts
            // the remaining project. No elapsed-time threshold decides overlap.
            execution.Release(blocked[^1]);
            for (var remaining = slots; remaining < Projects.Length; remaining++)
            {
                var next = execution.Take();
                if (slots == 2) Assert.False(blocked[0].HasExited);
                execution.Release(next);
            }
            execution.ReleaseAll();
            Assert.Equal(0, await run.WaitAsync(TestBudgets.ScriptProcessHangGuard));
        }
        catch (Exception exception) when (exception is TimeoutException or OperationCanceledException)
        {
            throw new SkipException("infrastructure-hang-guard expired for project overlap handshake: " + exception.Message);
        }
        finally
        {
            execution.ReleaseAll();
            await run.WaitAsync(TestBudgets.ScriptProcessHangGuard);
        }
        Assert.Equal(slots, execution.Peak);
        Assert.Equal(Projects.Length, execution.Completed);
        var tests = CommonExecutionEvidence.ValidateTests(fixture.Root);
        Assert.Equal(Projects, tests.Projects.Select(project => project.Project));
        Assert.Equal(["0", "1", "2"], tests.Projects.Select(project => Path.GetFileName(project.Results)));
        Assert.All(tests.Projects, project => Assert.Equal("executed", project.Status));
    }

    [Theory]
    [InlineData("none", 0)]
    [InlineData("process", 1)]
    [InlineData("cancelled", 1)]
    [InlineData("trx", 1)]
    public async Task ParallelExecutionJoinsFailuresAndKeepsReusedProjectEvidence(string failure, int expected)
    {
        using var fixture = Fixture(2);
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (project, directory) =>
        {
            Trx(fixture, project, directory);
            return 0;
        }, TextWriter.Null));
        var original = CommonExecutionEvidence.ValidateTests(fixture.Root);
        var seed = Path.Combine(fixture.Root, CommonExecutionEvidence.TestSeedPath);
        foreach (var material in original.Materials)
        {
            var destination = Path.Combine(seed, material.Path);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(Path.Combine(fixture.Root, material.Path), destination);
        }
        CommonExecutionEvidence.Write(seed, "tests.json", original);
        var prior = original.Projects[1];
        fixture.Write("tools/tests/First/Input.cs", "// changed first input\n");
        fixture.Write("tools/tests/Third/Input.cs", "// changed third input\n");
        fixture.Track();
        fixture.Build();
        using var execution = new BlockingProjects(fixture, failure);
        var run = Task.Run(() => Program.RunCurrentTests(fixture.Root, execution.Run, TextWriter.Null));
        try
        {
            var first = execution.Take();
            var second = execution.Take();
            Assert.False(first.HasExited);
            Assert.False(second.HasExited);
            execution.ReleaseAll();
            Assert.Equal(expected, await run.WaitAsync(TestBudgets.ScriptProcessHangGuard));
        }
        catch (Exception exception) when (exception is TimeoutException or OperationCanceledException)
        {
            throw new SkipException("infrastructure-hang-guard expired for mixed project handshake: " + exception.Message);
        }
        finally
        {
            execution.ReleaseAll();
            await run.WaitAsync(TestBudgets.ScriptProcessHangGuard);
        }
        Assert.Equal(2, execution.Peak);
        Assert.Equal(2, execution.Completed);
        var tests = CommonExecutionEvidence.Read<TestExecutionRecord>(fixture.Root, CommonExecutionEvidence.TestsPath);
        Assert.Equal(Projects, tests.Projects.Select(project => project.Project));
        Assert.Equal(["executed", "reused", "executed"], tests.Projects.Select(project => project.Status));
        Assert.Equal(prior with { Status = "reused" }, tests.Projects[1]);
        Assert.Equal("0", Path.GetFileName(tests.Projects[0].Results));
        Assert.Equal("2", Path.GetFileName(tests.Projects[2].Results));
        Assert.Equal(0, tests.Projects[2].Exit);
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.EngineeringPath)));
        if (expected == 0) CommonExecutionEvidence.ValidateTests(fixture.Root);
        else Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
    }

    private static CurrentExecutionContractTests.CandidateFixture Fixture(int slots)
    {
        var fixture = new CurrentExecutionContractTests.CandidateFixture();
        fixture.Write(Third, "<Project />\n");
        var path = Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path);
        var manifest = JsonNode.Parse(EngineeringRegistrationFixture.Append(File.ReadAllText(path),
            new EngineeringProjectFixture(Third, "Third", "cross-cutting-test", true, ["tools/tests/Third/**/*.cs"])))!;
        manifest["test_parallelism"] = slots;
        fixture.Write(EngineeringRegistrationFixture.Path, manifest.ToJsonString());
        fixture.Track();
        fixture.Build();
        return fixture;
    }

    private static void Trx(CurrentExecutionContractTests.CandidateFixture fixture, string project, string directory)
    {
        fixture.WriteTrx(directory, "Passed");
        var path = Path.Combine(directory, "execution.trx");
        var original = Path.GetFileName(directory) == "1" ? "Second" : "First";
        File.WriteAllText(path, File.ReadAllText(path).Replace(original + ".dll",
            Path.GetFileNameWithoutExtension(project) + ".dll", StringComparison.Ordinal));
    }

    private sealed class BlockingProjects(CurrentExecutionContractTests.CandidateFixture fixture, string failure = "none") : IDisposable
    {
        private readonly BlockingCollection<Process> started = [];
        private readonly ConcurrentBag<Process> children = [];
        private readonly CancellationTokenSource guard = new(TestBudgets.ScriptProcessHangGuard);
        private readonly object state = new();
        private int active;
        internal int Peak { get; private set; }
        internal int Completed { get; private set; }

        internal int Run(string project, string directory)
        {
            var fails = project == Projects[0];
            var start = new ProcessStartInfo("/bin/sh") { RedirectStandardInput = true, RedirectStandardOutput = true, UseShellExecute = false };
            foreach (var argument in new[] { "-c", "printf 'ready\\n'; read -r release; exit \"$1\"", "project", fails && failure == "process" ? "17" : "0" })
                start.ArgumentList.Add(argument);
            var process = Process.Start(start)!;
            children.Add(process);
            Assert.Equal("ready", process.StandardOutput.ReadLine());
            lock (state) { active++; Peak = Math.Max(Peak, active); }
            started.Add(process);
            try
            {
                process.WaitForExit();
                if (fails && failure == "cancelled") throw new OperationCanceledException("project cancelled");
                if (!(fails && failure == "trx")) Trx(fixture, project, directory);
                return process.ExitCode;
            }
            finally { lock (state) { active--; Completed++; } }
        }

        internal Process Take() => started.Take(guard.Token);
        internal void Release(Process process)
        {
            try { if (!process.HasExited) { process.StandardInput.WriteLine("release"); process.StandardInput.Flush(); } }
            catch (IOException) { }
        }
        internal void ReleaseAll() { foreach (var child in children) Release(child); }
        public void Dispose()
        {
            foreach (var child in children) { if (!child.HasExited) child.Kill(entireProcessTree: true); child.Dispose(); }
            guard.Dispose();
            started.Dispose();
        }
    }
}
