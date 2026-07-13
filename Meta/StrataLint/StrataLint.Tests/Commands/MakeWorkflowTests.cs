using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class MakeWorkflowTests
{
    private static readonly string[] Targets =
    [
        "help",
        "dotnet",
        "test",
        "lean",
        "build",
        "emit",
        "emit-check",
        "selftest",
        "gate",
        "worktree",
    ];

    [Fact]
    public void MakefileIsAThinCompleteDispatchTable()
    {
        var root = FindRepositoryRoot();
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));

        Assert.Contains(".DEFAULT_GOAL := help", makefile, StringComparison.Ordinal);
        var phony = Assert.Single(
            makefile.Split('\n'),
            static line => line.StartsWith(".PHONY:", StringComparison.Ordinal));
        Assert.Equal(Targets, phony[".PHONY:".Length..].Split(' ', StringSplitOptions.RemoveEmptyEntries));
        foreach (var target in Targets)
        {
            Assert.Matches(new Regex($"(?m)^{Regex.Escape(target)}:", RegexOptions.CultureInvariant), makefile);
            Assert.InRange(RecipeCount(makefile, target), 0, 1);
        }

        Assert.Contains("build: dotnet lean", makefile, StringComparison.Ordinal);
        Assert.Equal(0, RecipeCount(makefile, "build"));
        Assert.Contains("Meta/StrataLint/scripts/dotnet-build.sh", Recipe(makefile, "dotnet"), StringComparison.Ordinal);
        Assert.Contains("dotnet test", Recipe(makefile, "test"), StringComparison.Ordinal);
        Assert.Contains("lake build", Recipe(makefile, "lean"), StringComparison.Ordinal);
        Assert.Contains("Meta/StrataLint/scripts/scribe.sh emit", Recipe(makefile, "emit"), StringComparison.Ordinal);
        Assert.Contains("Meta/StrataLint/scripts/scribe.sh check", Recipe(makefile, "emit-check"), StringComparison.Ordinal);
        Assert.Contains("Meta/StrataLint/scripts/stratalint-selftest.sh", Recipe(makefile, "selftest"), StringComparison.Ordinal);
        Assert.Contains("Meta/StrataLint/scripts/local-harness-gate.sh", Recipe(makefile, "gate"), StringComparison.Ordinal);
        Assert.Contains("Meta/StrataLint/scripts/worktree-init.sh", Recipe(makefile, "worktree"), StringComparison.Ordinal);
    }

    [Fact]
    public void HelpRunsAndNamesEveryTarget()
    {
        var root = FindRepositoryRoot();
        var result = BoundedProcessRunner.Run(
            "make",
            ["help"],
            root,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        var output = System.Text.Encoding.UTF8.GetString(result.StandardOutput);
        Assert.All(Targets, target => Assert.Contains($"make {target}", output, StringComparison.Ordinal));
        Assert.Contains("values", output, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void CiAndLocalGateReuseCanonicalEntrypoints()
    {
        var root = FindRepositoryRoot();
        var workflow = File.ReadAllText(Path.Combine(root, ".github", "workflows", "ci.yml"));
        var localGate = File.ReadAllText(Path.Combine(root, "Meta", "StrataLint", "scripts", "local-harness-gate.sh"));

        Assert.Contains("make -C candidate dotnet", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C candidate test", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C candidate selftest", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C \"$CANDIDATE_ROOT\" emit-check", localGate, StringComparison.Ordinal);
        Assert.Contains("$JUDGE_ROOT/.github/scripts/harness-gate.sh", localGate, StringComparison.Ordinal);
        Assert.Contains("--candidate-lean-report", localGate, StringComparison.Ordinal);
        Assert.Contains("--baseline-lean-report", localGate, StringComparison.Ordinal);
    }

    [Fact]
    public void ScribeWrapperProducesCanonicalLeanReportBeforeEmission()
    {
        var root = FindRepositoryRoot();
        var script = File.ReadAllText(Path.Combine(root, "Meta", "StrataLint", "scripts", "scribe.sh"));
        var producerIndex = script.IndexOf("lean-inspector/inspect.sh", StringComparison.Ordinal);
        var emissionIndex = script.IndexOf("dotnet run", StringComparison.Ordinal);

        Assert.True(producerIndex >= 0, "scribe wrapper must name the canonical Lean producer");
        Assert.True(emissionIndex > producerIndex, "Lean report production must precede Scribe emission");
        Assert.Contains(".lake/build/stratalint/raw-lean-report.json", script, StringComparison.Ordinal);
        Assert.Contains("SCRIBE_USE_EXISTING_REPORT", script, StringComparison.Ordinal);
        Assert.DoesNotContain("CHECK_ARGS=()", script, StringComparison.Ordinal);
        Assert.Contains("run_scribe emit", script, StringComparison.Ordinal);
        Assert.Contains("run_scribe catalog", script, StringComparison.Ordinal);
        Assert.Contains("run_scribe emit-values", script, StringComparison.Ordinal);
    }

    [Fact]
    public void WorktreeAdapterRestoresToolPathBeforeResolvingRepositoryRoot()
    {
        var root = FindRepositoryRoot();
        var script = File.ReadAllText(Path.Combine(root, "Meta", "StrataLint", "scripts", "worktree-init.sh"));
        var pathIndex = script.IndexOf("export PATH=", StringComparison.Ordinal);
        var dirnameIndex = script.IndexOf("dirname", StringComparison.Ordinal);

        Assert.True(pathIndex >= 0, "worktree adapter must restore the process tool path");
        Assert.True(pathIndex < dirnameIndex, "tool PATH must be restored before dirname is invoked");
    }

    private static int RecipeCount(string makefile, string target) =>
        RecipeLines(makefile, target).Count;

    private static string Recipe(string makefile, string target) =>
        Assert.Single(RecipeLines(makefile, target));

    private static IReadOnlyList<string> RecipeLines(string makefile, string target)
    {
        var lines = makefile.Split('\n');
        var start = Array.FindIndex(lines, line => line.StartsWith(target + ":", StringComparison.Ordinal));
        Assert.True(start >= 0, $"target is absent: {target}");
        return lines
            .Skip(start + 1)
            .TakeWhile(static line => line.Length == 0 || line[0] == '\t')
            .Where(static line => line.StartsWith('\t'))
            .ToArray();
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
