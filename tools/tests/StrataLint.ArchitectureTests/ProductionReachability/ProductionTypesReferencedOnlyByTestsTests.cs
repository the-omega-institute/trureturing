namespace StrataLint.ArchitectureTests;

public sealed class ProductionTypesReferencedOnlyByTestsTests
{
    [Fact]
    public void ProductionTypesAreNotReferencedOnlyByTests()
    {
        var census = ProductionTestOnlyTypePolicy.InspectRepository(RepositoryLayout.FindRoot());
        var findings = census.Where(static finding => !finding.IsAllowlisted).ToArray();

        Assert.True(
            findings.Length == 0,
            "Production types whose non-declaration references all occur under tools/tests/ "
            + "(allowlisted census entries are retained below):"
            + Environment.NewLine
            + string.Join(Environment.NewLine, census.Select(Format)));
    }

    private static string Format(ProductionTestOnlyTypeFinding finding)
    {
        var references = finding.ReferencePaths.Count == 0
            ? "no non-declaration references"
            : string.Join(", ", finding.ReferencePaths);
        var allowlist = finding.AllowlistReason is null
            ? string.Empty
            : $" [allowlisted: {finding.AllowlistReason}]";

        return $"{finding.QualifiedName}{allowlist}; declared: "
            + $"{string.Join(", ", finding.DeclarationPaths)}; referenced: {references}";
    }
}
