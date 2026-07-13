namespace StrataLint.ArchitectureTests;

public sealed class RepositoryPathLiteralTests
{
    [Fact]
    public void RepositoryCSharpDoesNotCopyExistingRepositoryFilePaths()
    {
        var findings = RepositoryPathLiteralPolicy.InspectRepository(RepositoryLayout.FindRoot());

        Assert.True(
            findings.Count == 0,
            string.Join(
                Environment.NewLine,
                findings
                    .GroupBy(static finding => (finding.Path, finding.Value))
                    .Select(static group =>
                        $"{group.Key.Path}: {group.Key.Value} ({group.Count()} occurrences)")));
    }

    [Fact]
    public void ExistingMultisegmentPathLiteralIsRejectedByTheRedFixture()
    {
        const string source = """
            var path = "docs/develop/spec/synthetic.md";
            """;

        var finding = Assert.Single(RepositoryPathLiteralPolicy.InspectSource(
            "Meta/StrataLint/Synthetic.cs",
            source,
            new HashSet<string>(StringComparer.Ordinal)
            {
                "docs/develop/spec/synthetic.md",
            }));

        Assert.Contains("existing repository file", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CanonicalConstDefinitionAndItsConsumersAreAllowed()
    {
        const string source = """
            internal static class CanonicalPaths
            {
                internal const string Source = "docs/develop/spec/synthetic.md";

                internal static string Read() => Source;
            }
            """;

        Assert.Empty(RepositoryPathLiteralPolicy.InspectSource(
            "Meta/StrataLint/Synthetic.cs",
            source,
            new HashSet<string>(StringComparer.Ordinal)
            {
                "docs/develop/spec/synthetic.md",
            }));
    }

    [Fact]
    public void NonexistentPathAndCommentsAreNotRejected()
    {
        const string source = """
            // "docs/develop/spec/synthetic.md"
            var path = "docs/develop/spec/not-present.md";
            """;

        Assert.Empty(RepositoryPathLiteralPolicy.InspectSource(
            "Meta/StrataLint/Synthetic.cs",
            source,
            new HashSet<string>(StringComparer.Ordinal)
            {
                "docs/develop/spec/synthetic.md",
            }));
    }
}
