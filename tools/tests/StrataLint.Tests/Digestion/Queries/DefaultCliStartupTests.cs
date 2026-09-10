using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using Xunit.Abstractions;

namespace StrataLint.Tests;

public sealed class DefaultCliStartupTests(ITestOutputHelper output)
{
    [Fact]
    public void DefaultCliValidatesBranchOutsideRepositoryWithoutScribeInputs()
    {
        using var temporary = new TemporaryDirectory();
        var branch = $"{WorktreeCommand.CreationNamespace}/{WorktreeCommand.CreationKinds[0]}/startup";

        var result = RunCli(temporary.Path, "worktree", "validate-branch", "--branch", branch);

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        using var receipt = JsonDocument.Parse(result.StandardOutput);
        Assert.Equal("branch_validation", receipt.RootElement.GetProperty("event").GetString());
        Assert.Equal(branch, receipt.RootElement.GetProperty("branch").GetString());
        Assert.True(receipt.RootElement.GetProperty("canonical").GetBoolean());
    }

    [Fact]
    public void DefaultCliBulkCandidatesNeedNoLeanReportOrScribeDiscoveryFixtures()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        foreach (var (path, content) in fixture.Files)
        {
            var destination = Path.Combine(temporary.Path, path);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            TemporaryFileSystem.File.WriteAllText(destination, content);
        }
        ReviewRegressionTests.RunGit(temporary.Path, "init");
        ReviewRegressionTests.RunGit(temporary.Path, "add", ".");
        ReviewRegressionTests.RunGit(temporary.Path, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.test",
            "commit", "-m", "synthetic query baseline");

        var result = RunCli(temporary.Path, "digest-status", "--formalize-candidates");

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        using var candidates = JsonDocument.Parse(result.StandardOutput);
        Assert.Equal("stratalint-formalize-candidates-v5", candidates.RootElement.GetProperty("schema").GetString());
    }

    private ProcessOutput RunCli(string root, params string[] arguments)
    {
        var name = arguments[0] == "worktree"
            ? nameof(DefaultCliValidatesBranchOutsideRepositoryWithoutScribeInputs)
            : nameof(DefaultCliBulkCandidatesNeedNoLeanReportOrScribeDiscoveryFixtures);
        var lines = new List<string>();
        var probe = new DefaultCliStartupProbe(name, "parent", lines.Add);
        // Sibling of the fixture: diagnostic files must not enter its Git snapshot.
        var tracePath = root + ".startup-probe.jsonl";
        var executable = Path.Combine(AppContext.BaseDirectory, "StrataLint");
        var previousStart = BoundedProcessRunner.StartProcess.Value;
        var previousProbe = DefaultCliStartupProbe.Current.Value;
        DefaultCliStartupProbe.Current.Value = probe;
        BoundedProcessRunner.StartProcess.Value = process =>
        {
            if (process.StartInfo.FileName == executable && process.StartInfo.WorkingDirectory == root)
            {
                process.StartInfo.Environment[DefaultCliStartupProbe.PathVariable] = tracePath;
                process.StartInfo.Environment[DefaultCliStartupProbe.InvocationVariable] = name;
            }
            return previousStart?.Invoke(process) ?? process.Start();
        };
        try
        {
            probe.Runtime();
            probe.Fixture(root);
            probe.Resources("before-invocation");
            return TestProcessRunner.Run(executable, arguments, root,
                TestBudgets.LocalProcessHangGuard, 1024 * 1024);
        }
        finally
        {
            BoundedProcessRunner.StartProcess.Value = previousStart;
            DefaultCliStartupProbe.Current.Value = previousProbe;
            probe.Mark("invocation-finally");
            probe.Collect(tracePath, lines.Add);
            probe.Identities(AppContext.BaseDirectory);
            probe.Cleanup(tracePath);
            // xUnit retains success/skip output in TRX. EngineeringScope forwards
            // these diagnostic records before deleting its temporary TRX.
            foreach (var line in lines)
            {
                DefaultCliStartupProbe.Emit(output.WriteLine, line);
            }
        }
    }
}
