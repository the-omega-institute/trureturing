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

        Assert.Equal(18, File.ReadLines(path).Count(static line =>
            line.Contains("// banned-api-proof", StringComparison.Ordinal)));
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
