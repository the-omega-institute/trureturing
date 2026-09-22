using StrataLint.EngineeringScope;
using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.InspectionIntegration.Tests;

public sealed class MarkdownInspectionScopeTests
{
    [Theory]
    [InlineData("tools/StrataLint.Engine/Rules/CurrentCapacity.cs", false)]
    [InlineData("tools/StrataLint.Cli/Commands/FileMap/FileMapPolicy.cs", false)]
    [InlineData("tools/StrataLint.Cli/Admission/ProductionCliEnvironment.CurrentChecks.cs", false)]
    [InlineData("tools/StrataLint.EngineeringScope/CommonExecutionEvidence.Checks.cs", false)]
    [InlineData("tools/Trureturing.Truth/Program.cs", false)]
    [InlineData("Meta/ReportProducers/lean-report.json", false)]
    [InlineData("Meta/ReportConsumers/lean-report.json", false)]
    [InlineData("lean-toolchain", false)]
    [InlineData("lake-manifest.json", false)]
    [InlineData("tools/Architecture/BannedSymbols.txt", false)]
    [InlineData("tools/StrataLint.Scribe/Verification/MarkdownMath.cs", true)]
    [InlineData("tools/StrataLint.Scribe/Verification/MarkdownFormulaScope.cs", true)]
    [InlineData("tools/StrataLint.Scribe/Verification/KatexParser.cs", true)]
    [InlineData("tools/StrataLint.Scribe/Vendor/Katex/katex.min.js", true)]
    [InlineData("tools/StrataLint.Scribe/Writers/CanonicalMarkdownWriter.cs", true)]
    [InlineData("tools/StrataLint.Scribe/Emission/ScribeCli.cs", true)]
    [InlineData("tools/StrataLint.InspectionScope/MarkdownInspectionScope.cs", true)]
    [InlineData("Meta/ci-checks.json", true)]
    [InlineData("Directory.Build.targets", true)]
    public void RepositoryWhitelistSelectsWholeMarkdownOnlyForItsRegisteredProgramInputs(string changed, bool whole)
    {
        var (registration, paths) = RepositoryRegistration();
        var selected = MarkdownInspectionScope.Select(registration, [changed],
            ["Blueprint/D5/First.md", "Blueprint/D5/Second.md", "docs/theory/Other.md"], paths);
        Assert.Equal(whole, selected.WholeTree);
        Assert.Equal(whole ? new[] { "Blueprint/D5/First.md", "Blueprint/D5/Second.md" } : [], selected.Paths);
    }

    [Fact]
    public void RepositoryWhitelistKeepsChangedDocumentsAlongsideUnrelatedJudgeChanges()
    {
        var (registration, paths) = RepositoryRegistration();
        var selected = MarkdownInspectionScope.Select(registration,
            ["tools/StrataLint.Engine/Rules/CurrentCapacity.cs", "Blueprint/D5/First.md", "Blueprint/D5/Removed.scribe.cs"],
            ["Blueprint/D5/First.md", "Blueprint/D5/Unchanged.md"], paths);
        Assert.False(selected.WholeTree);
        Assert.Equal(new[] { "Blueprint/D5/First.md", "Blueprint/D5/Removed.scribe.cs" }, selected.Paths);
    }

    private static (RegisteredMarkdownScope Registration, string[] Paths) RepositoryRegistration()
    {
        using var document = JsonDocument.Parse(File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "Meta/ci-checks.json")));
        var check = document.RootElement.GetProperty("checks").EnumerateArray().Single(row => row.GetProperty("id").GetString() == "scribe-markdown");
        var scope = check.GetProperty("markdown_scope");
        return (new(Strings(scope.GetProperty("whole_tree_inputs")), Strings(scope.GetProperty("changed_inputs"))), Strings(check.GetProperty("path_inventory")));

        static string[] Strings(JsonElement values) => values.EnumerateArray().Select(value => value.GetString()!).ToArray();
    }
}
