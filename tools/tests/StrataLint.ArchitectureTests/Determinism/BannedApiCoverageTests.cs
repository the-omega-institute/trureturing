namespace StrataLint.ArchitectureTests;

public sealed class BannedApiCoverageTests
{
    [Fact]
    public void CompileFailProofMarksEveryExpectedDiagnosticLine()
    {
        var path = Path.Combine(
            RepositoryLayout.FindRoot(),
            "tools", "tests", "BannedApiCompileFailProof",
            "BannedApiViolations.cs");

        Assert.Equal(21, File.ReadLines(path).Count(static line =>
            line.Contains("// banned-api-proof", StringComparison.Ordinal)));
    }

    [Fact]
    public void DeterminismBanNamesEveryWallClockAndDelaySymbol()
    {
        var path = Path.Combine(
            RepositoryLayout.FindRoot(),
            "tools", "Architecture", "BannedSymbols.Determinism.txt");
        var entries = File.ReadAllLines(path).ToHashSet(StringComparer.Ordinal);

        Assert.Contains(
            "M:System.Threading.Thread.Sleep;Use an injected synchronization primitive outside deterministic tests.",
            entries);
        Assert.Contains(
            "M:System.Threading.Tasks.Task.Delay;Use virtual time or an injected synchronization primitive.",
            entries);
        Assert.Contains(
            "T:System.Diagnostics.Stopwatch;Do not make test verdicts or diagnostics depend on machine speed.",
            entries);
    }

    [Fact]
    public void DeterminismBanIsAttachedToEveryVerdictProject()
    {
        var root = RepositoryLayout.FindRoot();
        var projects = new[]
        {
            "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
            "tools/tests/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj",
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
        };

        Assert.All(projects, relativePath =>
        {
            var project = File.ReadAllText(Path.Combine(
                root,
                relativePath.Replace('/', Path.DirectorySeparatorChar)));
            Assert.Contains(
                "Microsoft.CodeAnalysis.BannedApiAnalyzers",
                project,
                StringComparison.Ordinal);
            Assert.Contains(
                "BannedSymbols.Determinism.txt",
                project,
                StringComparison.Ordinal);
        });
    }

    [Fact]
    public void EngineeringCiComparesEveryMarkedLineWithAnRs0030Diagnostic()
    {
        var path = Path.Combine(RepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml");
        var workflow = File.ReadAllText(path);

        Assert.Contains("mapfile -t expected_lines", workflow, StringComparison.Ordinal);
        Assert.Contains("grep -nF \"// banned-api-proof\"", workflow, StringComparison.Ordinal);
        Assert.Contains("mapfile -t actual_lines", workflow, StringComparison.Ordinal);
        Assert.Contains("error RS0030", workflow, StringComparison.Ordinal);
        Assert.Contains(
            "test \"${#actual_lines[@]}\" -eq \"${#expected_lines[@]}\"",
            workflow,
            StringComparison.Ordinal);
    }
}
