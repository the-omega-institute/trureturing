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
                "schema_version: 3\nledger: theory-digestion-v1\nsources: []\n"
                + "ticket_index:\n  - case_id: SYNTHETIC-CASE\n    gid: synthetic/gid\n");
            var repositoryRoot = RepositoryLayout.FindRoot();
            File.Copy(
                Path.Combine(repositoryRoot, "Meta", "registry.yaml"),
                Path.Combine(root, "Meta", "registry.yaml"));
            File.Copy(
                Path.Combine(repositoryRoot, "Meta", "domains.yaml"),
                Path.Combine(root, "Meta", "domains.yaml"));
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

    [Theory]
    [InlineData("S0")]
    [InlineData("S4")]
    public void RegisteredDomainDictionaryEntryIsRejectedByTheRedFixture(string stratum)
    {
        var source = $$"""
            var copied = new Dictionary<string, string>
            {
                ["Carrier"] = "{{stratum}}",
            };
            """;
        var domains = new[]
        {
            (Name: "Carrier", Stratum: "S0"),
        };

        var finding = Assert.Single(CanonicalSourceDuplicationPolicy.InspectDomainMappings(
            "Meta/StrataLint/Synthetic.cs",
            source,
            domains));

        Assert.Contains("Meta/domains.yaml", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SeparateDomainAndStratumLiteralsAreNotTreatedAsADomainMap()
    {
        const string source = """
            const string domain = "Carrier";
            const string stratum = "S0";
            """;
        var domains = new[]
        {
            (Name: "Carrier", Stratum: "S0"),
        };

        Assert.Empty(CanonicalSourceDuplicationPolicy.InspectDomainMappings(
            "Meta/StrataLint/Synthetic.cs",
            source,
            domains));
    }
}
