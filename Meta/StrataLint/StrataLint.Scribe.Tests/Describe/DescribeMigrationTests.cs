using System.Text.Json;

namespace StrataLint.Scribe.Tests;

public sealed class DescribeMigrationTests
{
    [Fact]
    public void RepositoryMigrationHasFifteenTypedNodesAndPreservesTwentyFourFormulaSlots()
    {
        var root = FindRepositoryRoot();
        var report = DescribeReport.Build(
            root,
            DocumentDefinitions.All.Select(static definition => definition.Document));

        Assert.Equal(15, report.NodeStats.Total);
        Assert.Equal(24, report.NodeStats.FormulaContentSlots);
        Assert.Equal(1, report.NodeStats.FormulaStatements);
        Assert.Equal(14, report.NodeStats.LeanStatements);
        Assert.Equal(7, report.NodeStats.ByKind["proposition"]);
        Assert.Equal(7, report.NodeStats.ByKind["theorem"]);
        Assert.Equal(1, report.NodeStats.ByKind["example"]);
        Assert.Equal(13, report.NodeStats.ByProvenance["repo-derived"]);
        Assert.Equal(2, report.NodeStats.ByProvenance["literature-attested"]);
        Assert.Equal(0, report.OpenCount);
        Assert.Empty(report.SuspectedNovel);
        Assert.Empty(report.RedFindings);
    }

    [Fact]
    public void ResidualPilotNodesUseTypedLeanStatementsAndDiligentLiteratureProvenance()
    {
        var expected = new[]
        {
            (
                Document: "D5/S0/Carrier/GoldenRatio",
                Declaration: "D5/S0/Carrier/GoldenRatio.golden_ratio_spec"),
            (
                Document: "D5/S1/Scale/FibonacciEigen",
                Declaration: "D5/S1/Scale/FibonacciEigen.fibonacci_substitution_spec"),
        };

        foreach (var item in expected)
        {
            var document = Assert.Single(
                DocumentDefinitions.All.Select(static definition => definition.Document),
                document => document.Header.Gid.Value == item.Document);
            var describe = Assert.Single(document.Content.Items.OfType<DocumentBlock.Describe>());
            var statement = Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);

            Assert.Equal(item.Declaration, statement.Value.Value);
            Assert.Equal(DescribeProvenanceKind.LiteratureAttested, describe.Provenance.Kind);
            Assert.Equal("D5/L/koshy2001fibonacci", describe.Provenance.LiteratureReference?.Value);
        }
    }

    [Fact]
    public void LegacyNarrativeNodeTypesAreAbsentAfterTheSingleStepMigration()
    {
        var nestedNames = typeof(DocumentBlock).GetNestedTypes()
            .Select(static type => type.Name)
            .ToHashSet(StringComparer.Ordinal);

        Assert.DoesNotContain("Proposition", nestedNames);
        Assert.DoesNotContain("Theorem", nestedNames);
        Assert.DoesNotContain("ComputedValue", nestedNames);
        Assert.DoesNotContain("RenderedStatement", nestedNames);
    }

    [Fact]
    public void DescribeReportVerbReturnsTheMachineQueryableLedger()
    {
        var output = new StringWriter();
        var error = new StringWriter();

        var exit = ScribeCli.Run(
            ["describe-report", "--json"],
            FindRepositoryRoot(),
            output,
            error,
            LeanReportFixture.ForDocuments(
                DocumentDefinitions.All.Select(static definition => definition.Document)));

        Assert.Equal(0, exit);
        Assert.Equal(string.Empty, error.ToString());
        using var document = JsonDocument.Parse(output.ToString());
        Assert.Equal("DESCRIBE-NODES", document.RootElement.GetProperty("case_id").GetString());
        Assert.Equal(15, document.RootElement.GetProperty("node_stats").GetProperty("total").GetInt32());
        Assert.Equal(0, document.RootElement.GetProperty("open_count").GetInt32());
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "global.json"))
                && Directory.Exists(Path.Combine(current.FullName, "Blueprint")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
