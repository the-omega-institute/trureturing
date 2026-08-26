using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class EngineeringScopeScriptTests
{
    private const string ScriptPath = "tools/scripts/workflow/engineering-scope.sh";

    [Fact]
    public void EngineeringChangesRunFullEngineering()
    {
        var decision = RunPullRequestDecision("tools/scripts/preflight.sh");

        Assert.Equal("full", decision["decision"]);
        Assert.Equal("true", decision["run"]);
        Assert.Equal("1", decision["changed_count"]);
        Assert.Equal("0", decision["disjoint_count"]);
    }

    [Fact]
    public void DigestionOnlyChangesSkipEngineering()
    {
        var decision = RunPullRequestDecision("Meta/Digestion/atoms/scope-probe.json");

        Assert.Equal("none", decision["decision"]);
        Assert.Equal("false", decision["run"]);
    }

    [Fact]
    public void DocsOnlyChangesSkipEngineering()
    {
        var decision = RunPullRequestDecision("docs/develop/scope-probe.md");

        Assert.Equal("none", decision["decision"]);
        Assert.Equal("false", decision["run"]);
    }

    [Fact]
    public void FrozenOnlyChangesSkipEngineering()
    {
        var decision = RunPullRequestDecision("Golden/Frozen/accepted/scope-probe.json");

        Assert.Equal("none", decision["decision"]);
        Assert.Equal("false", decision["run"]);
    }

    [Fact]
    public void AllWhitelistedChangesSkipEngineering()
    {
        var decision = RunPullRequestDecision(
            "Meta/Digestion/atoms/scope-probe.json",
            "docs/develop/scope-probe.md",
            "Golden/Frozen/accepted/scope-probe.json");

        Assert.Equal("none", decision["decision"]);
        Assert.Equal("false", decision["run"]);
        Assert.Equal("3", decision["changed_count"]);
        Assert.Equal("3", decision["disjoint_count"]);
    }

    [Fact]
    public void MixedDigestionAndLeanChangesRunFullEngineering()
    {
        var decision = RunPullRequestDecision(
            "Meta/Digestion/atoms/scope-probe.json",
            "D5/S0/ScopeProbe.lean");

        Assert.Equal("full", decision["decision"]);
        Assert.Equal("true", decision["run"]);
        Assert.Equal("2", decision["changed_count"]);
        Assert.Equal("1", decision["disjoint_count"]);
    }

    [Fact]
    public void EmptyDeltaRunsFullEngineering()
    {
        var decision = RunPullRequestDecision();

        Assert.Equal("full", decision["decision"]);
        Assert.Equal("true", decision["run"]);
        Assert.Equal("0", decision["changed_count"]);
        Assert.Equal("0", decision["disjoint_count"]);
    }

    [Fact]
    public void DevPushAlwaysRunsFullEngineering()
    {
        using var repository = CreateRepository("Meta/Digestion/atoms/scope-probe.json");

        var decision = RunDecision(repository.Path, "push");

        Assert.Equal("full", decision["decision"]);
        Assert.Equal("true", decision["run"]);
        Assert.Equal("dev push always runs the full engineering check", decision["reason"]);
    }

    [Fact]
    public void WorkflowConsumesBaseOwnedCanonicalEngineeringPredicate()
    {
        var workflow = ReadWorkflow();

        Assert.Contains(
            "git -C candidate archive HEAD^1 -- tools/scripts/workflow/engineering-scope.sh | tar -xO > \"$scope_script\"",
            workflow,
            StringComparison.Ordinal);
        Assert.Contains("/bin/bash \"$scope_script\"", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("StrataLint.EngineeringScope", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("engineering_root", workflow, StringComparison.Ordinal);
    }

    [Fact]
    public void PreflightConsumesCanonicalEngineeringPredicate()
    {
        var preflight = ReadPreflight();

        Assert.Contains(
            "/bin/bash \"$ROOT/tools/scripts/workflow/engineering-scope.sh\"",
            preflight,
            StringComparison.Ordinal);
    }

    private static string ReadWorkflow() =>
        File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            ".github/workflows/ci.yml"));

    private static string ReadPreflight() =>
        File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools/scripts/preflight.sh"));

    private static IReadOnlyDictionary<string, string> RunPullRequestDecision(params string[] paths)
    {
        using var repository = CreateRepository(paths);
        return RunDecision(repository.Path, "pull-request");
    }

    private static TemporaryDirectory CreateRepository(params string[] paths)
    {
        var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init", "--quiet", "--initial-branch=fixture");
        ReviewRegressionTests.RunGit(repository.Path, "config", "user.email", "scope@example.invalid");
        ReviewRegressionTests.RunGit(repository.Path, "config", "user.name", "Engineering Scope Tests");
        File.WriteAllText(Path.Combine(repository.Path, "README.md"), "base\n", new UTF8Encoding(false));
        ReviewRegressionTests.RunGit(repository.Path, "add", "README.md");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "--quiet", "-m", "base");

        foreach (var path in paths)
        {
            var absolute = Path.Combine(repository.Path, path);
            Directory.CreateDirectory(Path.GetDirectoryName(absolute)!);
            File.WriteAllText(absolute, path + "\n", new UTF8Encoding(false));
        }

        if (paths.Length == 0)
        {
            ReviewRegressionTests.RunGit(repository.Path, "commit", "--quiet", "--allow-empty", "-m", "empty");
        }
        else
        {
            ReviewRegressionTests.RunGit(repository.Path, "add", ".");
            ReviewRegressionTests.RunGit(repository.Path, "commit", "--quiet", "-m", "candidate");
        }

        return repository;
    }

    private static IReadOnlyDictionary<string, string> RunDecision(string repository, string mode)
    {
        var root = TestRepositoryLayout.FindRoot();
        using var output = new TemporaryDirectory();
        var resultFile = Path.Combine(output.Path, "result");
        var result = BoundedProcessRunner.Run(
            "/bin/bash",
            [
                Path.Combine(root, ScriptPath),
                "--repository",
                repository,
                "--mode",
                mode,
                "--result-file",
                resultFile,
            ],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.True(
            result.ExitCode == 0,
            $"scope script exited {result.ExitCode}\nstdout:\n{Encoding.UTF8.GetString(result.StandardOutput)}"
                + $"\nstderr:\n{Encoding.UTF8.GetString(result.StandardError)}");
        Assert.True(File.Exists(resultFile), "scope script did not write its result file");
        return File.ReadAllLines(resultFile).ToDictionary(
            static line => line[..line.IndexOf('=')],
            static line => line[(line.IndexOf('=') + 1)..],
            StringComparer.Ordinal);
    }
}
