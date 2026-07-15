using System.Text.Json;

namespace StrataLint.Scribe.Tests;

public sealed class DescribeMigrationTests
{
    [Fact]
    public void RepositoryMigrationHasThirteenTypedNodesAndPreservesTwentyFourFormulaSlots()
    {
        var root = FindRepositoryRoot();
        var report = DescribeReport.Build(
            root,
            DocumentDefinitions.All.Select(static definition => definition.Document));

        Assert.Equal(13, report.NodeStats.Total);
        Assert.Equal(24, report.NodeStats.FormulaContentSlots);
        Assert.Equal(1, report.NodeStats.FormulaStatements);
        Assert.Equal(12, report.NodeStats.LeanStatements);
        Assert.Equal(7, report.NodeStats.ByKind["proposition"]);
        Assert.Equal(5, report.NodeStats.ByKind["theorem"]);
        Assert.Equal(1, report.NodeStats.ByKind["example"]);
        Assert.Equal(13, report.NodeStats.ByProvenance["repo-derived"]);
        Assert.Equal(0, report.OpenCount);
        Assert.Empty(report.SuspectedNovel);
        Assert.Empty(report.RedFindings);
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
        Assert.Equal(13, document.RootElement.GetProperty("node_stats").GetProperty("total").GetInt32());
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
