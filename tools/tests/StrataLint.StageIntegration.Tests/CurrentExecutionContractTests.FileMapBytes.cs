using System.Diagnostics;
using System.Text.Json.Nodes;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.StageIntegration.Tests;

public sealed partial class CurrentExecutionContractTests
{
    [Theory]
    [InlineData("Meta/FILEMAP.toml", false)]
    [InlineData("Meta/FILEMAP.toml", true)]
    [InlineData("README.md", false)]
    [InlineData("README.md", true)]
    public void RepositoryTextVerdictChangesInvalidateExecutionAndOldTrx(string path, bool replayOldTrx)
    {
        using var fixture = new ExecutionFixture();
        var registration = JsonNode.Parse(File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), EngineeringRegistrationFixture.Path)))!;
        var declaration = registration["projects"]!.AsArray().Single(row => row!["path"]!.ToString()
            == "tools/tests/StrataLint.WorktreeContract.Tests/StrataLint.WorktreeContract.Tests.csproj")!;
        EditRegistration(fixture, rows =>
        {
            foreach (var field in new[] { "execution_inputs", "execution_excludes", "execution_filemap_paths" })
                rows[0]![field] = declaration[field]!.DeepClone();
            rows[1]!["execution_inputs"] = new JsonArray("Meta/FILEMAP.toml");
            rows[1]!["execution_filemap_paths"] = new JsonArray("docs/virtual.md");
        });
        fixture.Write("Meta/FILEMAP.toml", "[[files]]\npattern = \"docs/virtual.md\"\nrequire = []\n");
        fixture.Write("README.md", "original documentation\n");
        fixture.Track();
        var calls = new List<string>();
        int Run(string project, string results)
        {
            calls.Add(project);
            var passed = project == ExecutionFixture.Second || ScanRepositoryText(fixture).Exit == 1;
            fixture.WriteTrx(results, passed ? "Passed" : "Failed");
            return passed ? 0 : 1;
        }
        Assert.Equal(1, ScanRepositoryText(fixture).Exit);
        fixture.Build();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, Run, TextWriter.Null));
        Assert.Equal([ExecutionFixture.First, ExecutionFixture.Second], calls);
        var prior = CommonExecutionEvidence.ValidateTests(fixture.Root);
        Seed(fixture);

        // The same real grep used by the repository contract must see this text,
        // including when it is only a TOML comment. Keep the source itself clean.
        File.AppendAllText(Path.Combine(fixture.Root, path), "# cp " + string.Concat('-', 'c') + " fixture\n");
        var scan = ScanRepositoryText(fixture);
        Assert.Equal(0, scan.Exit);
        Assert.StartsWith(path + ":", scan.Output, StringComparison.Ordinal);
        var build = fixture.Build();
        if (replayOldTrx)
        {
            CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.TestsPath, prior with
            {
                Candidate = build.Candidate,
                Round = build.Round,
                Projects = prior.Projects.Select(project => project with { Status = "reused" }).ToArray(),
            });
            Assert.Equal("test input identity mismatch: " + ExecutionFixture.First,
                Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root)).Message);
            Assert.Equal("test input identity mismatch: " + ExecutionFixture.First,
                Assert.Throws<InvalidDataException>(() => AcceptEngineering(fixture)).Message);
            return;
        }

        calls.Clear();
        using var output = new StringWriter();
        var exit = Program.RunCurrentTests(fixture.Root, Run, output);
        var current = CommonExecutionEvidence.Read<TestExecutionRecord>(fixture.Root, CommonExecutionEvidence.TestsPath);
        Assert.Equal(prior.Projects[1] with { Status = "reused" }, current.Projects[1]);
        Assert.Equal(1, exit);
        Assert.Equal([ExecutionFixture.First], calls);
        Assert.NotEqual(prior.Projects[0].InputFingerprint, current.Projects[0].InputFingerprint);
        Assert.Equal("executed", current.Projects[0].Status);
        Assert.Equal(1, current.Projects[0].Exit);
        Assert.Contains("test input identity mismatch: " + ExecutionFixture.First, output.ToString(), StringComparison.Ordinal);
        Assert.Equal("test project failed: " + ExecutionFixture.First + ": TRX run summary did not succeed: "
            + Path.Combine(fixture.Root, current.Projects[0].Results, "execution.trx"),
            Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root)).Message);
    }

    [Theory]
    [InlineData("comment", false)]
    [InlineData("unrelated-row", false)]
    [InlineData("queried-row", true)]
    public void ExplicitFileMapQueriesKeepTheirProjectionIdentity(string mutation, bool invalidates)
    {
        using var fixture = new ExecutionFixture();
        const string filemap = "[[files]]\npattern = \"docs/virtual.md\"\nrequire = []\n";
        fixture.Write("Meta/FILEMAP.toml", filemap);
        EditRegistration(fixture, rows =>
        {
            rows[0]!["execution_inputs"] = new JsonArray("Meta/FILEMAP.toml");
            rows[0]!["execution_filemap_paths"] = new JsonArray("docs/virtual.md");
        });
        fixture.Track();
        Execute(fixture);
        Seed(fixture);
        var prior = CommonExecutionEvidence.ValidateTests(fixture.Root);
        fixture.Write("Meta/FILEMAP.toml", mutation switch
        {
            "comment" => filemap + "# cp " + string.Concat('-', 'c') + " fixture\n",
            "unrelated-row" => filemap + "[[files]]\npattern = \"unrelated/**\"\nrequire = []\n",
            _ => filemap.Replace("require = []", "require = [\"engineering\"]", StringComparison.Ordinal),
        });
        Assert.Equal(invalidates ? [ExecutionFixture.First] : [], Execute(fixture));
        var current = CommonExecutionEvidence.ValidateTests(fixture.Root);
        if (invalidates) Assert.NotEqual(prior.Projects[0].InputFingerprint, current.Projects[0].InputFingerprint);
        else Assert.Equal(prior.Projects[0] with { Status = "reused" }, current.Projects[0]);
        Assert.Equal(prior.Projects[1] with { Status = "reused" }, current.Projects[1]);
        AcceptEngineering(fixture);
        CommonExecutionEvidence.ValidateEngineering(fixture.Root);
    }

    [Theory]
    [InlineData("README.md", false)]
    [InlineData("Meta/FILEMAP.toml", false)]
    [InlineData("Makefile", true)]
    [InlineData("tools/Makefile", true)]
    [InlineData("tools/scripts/linkage-probe.sh", true)]
    [InlineData(".github/scripts/linkage-probe.sh", true)]
    public void CliLinkageRuntimeInputsExcludeUnrelatedRepositoryText(string path, bool invalidates)
    {
        using var fixture = new ExecutionFixture();
        var registration = JsonNode.Parse(File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), EngineeringRegistrationFixture.Path)))!;
        var declaration = registration["projects"]!.AsArray().Single(row => row!["path"]!.ToString()
            == "tools/tests/StrataLint.RepositoryContract.Tests/StrataLint.RepositoryContract.Tests.csproj")!;
        EditRegistration(fixture, rows =>
        {
            foreach (var field in new[] { "execution_inputs", "execution_excludes", "execution_filemap_paths" })
                rows[0]![field] = declaration[field]!.DeepClone();
        });
        foreach (var input in new[] {
            "README.md", "Meta/FILEMAP.toml", "Makefile", "tools/Makefile",
            "tools/scripts/linkage-probe.sh", ".github/scripts/linkage-probe.sh",
        }) fixture.Write(input, "registered fixture input\n");
        fixture.Track();
        Execute(fixture);
        Seed(fixture);
        var prior = CommonExecutionEvidence.ValidateTests(fixture.Root);
        File.AppendAllText(Path.Combine(fixture.Root, path), "changed caller bytes\n");
        Assert.Equal(invalidates ? [ExecutionFixture.First] : [], Execute(fixture));
        var current = CommonExecutionEvidence.ValidateTests(fixture.Root);
        if (invalidates) Assert.NotEqual(prior.Projects[0].InputFingerprint, current.Projects[0].InputFingerprint);
        else Assert.Equal(prior.Projects[0] with { Status = "reused" }, current.Projects[0]);
        Assert.Equal(prior.Projects[1] with { Status = "reused" }, current.Projects[1]);
        AcceptEngineering(fixture);
    }

    private static (int Exit, string Output) ScanRepositoryText(ExecutionFixture fixture)
    {
        var start = new ProcessStartInfo("git")
        {
            WorkingDirectory = fixture.Root, RedirectStandardOutput = true, RedirectStandardError = true,
        };
        var cloneFlag = string.Concat('-', 'c');
        var recursiveFlag = string.Concat('-', 'R');
        foreach (var argument in new[] { "grep", "-n", "-I", "-e", $"cp {cloneFlag}", "-e", $"\"{cloneFlag}\", \"{recursiveFlag}\"", "--", "." })
            start.ArgumentList.Add(argument);
        using var process = Process.Start(start)!;
        var stdout = process.StandardOutput.ReadToEndAsync();
        var stderr = process.StandardError.ReadToEndAsync();
        try
        {
            Assert.True(process.WaitForExit((int)TestBudgets.ScriptProcessHangGuard.TotalMilliseconds));
            Assert.Equal("", stderr.GetAwaiter().GetResult());
            return (process.ExitCode, stdout.GetAwaiter().GetResult());
        }
        finally
        {
            if (!process.HasExited) { process.Kill(entireProcessTree: true); process.WaitForExit(); }
        }
    }
}
