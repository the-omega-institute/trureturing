namespace StrataLint.ArchitectureTests;

public sealed class CanonicalSourceDuplicationTests
{
    [Fact]
    public void RepositoryCSharpDoesNotCopyCanonicalBackfillTicketMappings()
    {
        Assert.Empty(CanonicalSourceDuplicationPolicy.InspectRepository(RepositoryLayout.FindRoot()));
    }

    [Fact]
    public void RepositoryScanIncludesCSharpOutsideTheHarnessTree()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-canonical-source-" + Guid.NewGuid().ToString("N"));
        try
        {
            Directory.CreateDirectory(Path.Combine(root, "Meta", "StrataLint"));
            File.WriteAllText(
                Path.Combine(root, "Meta", "BACKFILL.yaml"),
                "ticket_index:\n  - case_id: SYNTHETIC-CASE\n    gid: synthetic/gid\n");
            var blueprint = Path.Combine(root, "Blueprint");
            Directory.CreateDirectory(blueprint);
            File.WriteAllText(
                Path.Combine(blueprint, "Synthetic.scribe.cs"),
                "var copied = new Dictionary<string, string> { [\"synthetic/gid\"] = \"SYNTHETIC-CASE\" };\n");

            var finding = Assert.Single(CanonicalSourceDuplicationPolicy.InspectRepository(root));

            Assert.Equal("Blueprint/Synthetic.scribe.cs", finding.Path);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    [Theory]
    [InlineData("[\"synthetic/gid\"] = \"SYNTHETIC-CASE\"")]
    [InlineData("[\"synthetic/gid\"] = [\"SYNTHETIC-CASE\"]")]
    [InlineData("[\"synthetic/gid\"] = new[] { \"SYNTHETIC-CASE\" }")]
    public void CanonicalTicketDictionaryEntryIsRejectedByTheRedFixture(string entry)
    {
        var source = $$"""
            var copied = new Dictionary<string, object>
            {
                {{entry}},
            };
            """;
        var tickets = new[]
        {
            (CaseId: "SYNTHETIC-CASE", Gid: "synthetic/gid"),
        };

        var finding = Assert.Single(CanonicalSourceDuplicationPolicy.InspectSource(
            "Meta/StrataLint/Synthetic.cs",
            source,
            tickets));

        Assert.Contains("Meta/BACKFILL.yaml", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SeparateDiagnosticLiteralsAreNotTreatedAsATicketMap()
    {
        const string source = """
            const string diagnostic = "SYNTHETIC-CASE";
            const string path = "synthetic/gid";
            """;
        var tickets = new[]
        {
            (CaseId: "SYNTHETIC-CASE", Gid: "synthetic/gid"),
        };

        Assert.Empty(CanonicalSourceDuplicationPolicy.InspectSource(
            "Meta/StrataLint/Synthetic.cs",
            source,
            tickets));
    }
}
