using StrataLint.Engine;
using StrataLint.TestSupport;

namespace StrataLint.Tests;

public sealed class TheoryDocumentCapacityTests
{
    private const string Document = "docs/develop/theory/Fixture.md";
    private static readonly RuleId CapacityRule = RuleId.CreateKnown(3);

    [Theory]
    [InlineData(5000, false)]
    [InlineData(5001, true)]
    public void AddedDocumentUsesItsOwnHardLimit(int lines, bool rejected)
    {
        var fixture = new RuleFixture();
        fixture.Files[Document] = Lines(lines);
        fixture.Changes.Add(Document);

        var diagnostics = RuleCatalog.Default.EvaluateSingle(CapacityRule, fixture.Build()).Diagnostics;

        if (!rejected)
        {
            Assert.Empty(diagnostics);
            return;
        }

        var finding = Assert.Single(diagnostics);
        Assert.Equal(Document, finding.Path);
        Assert.Equal(AdmissionEffect.Block, finding.AdmissionEffect);
        Assert.Contains("5001 lines (hard limit 5000)", finding.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(4999, 5000, false)]
    [InlineData(5000, 5001, true)]
    [InlineData(6000, 5001, true)]
    [InlineData(6000, 5000, false)]
    public void ModifiedDocumentIsJudgedByCandidateTotal(int baselineLines, int candidateLines, bool rejected)
    {
        var fixture = new RuleFixture();
        fixture.Baseline[Document] = Lines(baselineLines);
        fixture.Files[Document] = Lines(candidateLines);
        fixture.Changes.Add(Document);

        var diagnostics = RuleCatalog.Default.EvaluateDeltaSingle(CapacityRule, fixture.Build()).Diagnostics;

        Assert.Equal(rejected, diagnostics.Any(diagnostic => diagnostic.Path == Document
            && diagnostic.AdmissionEffect == AdmissionEffect.Block));
    }

    [Theory]
    [InlineData("\n", true)]
    [InlineData("\n", false)]
    [InlineData("\r\n", true)]
    [InlineData("\r\n", false)]
    public void BlankLinesCountAndTrailingTerminatorDoesNotAddALine(string newline, bool trailingTerminator)
    {
        foreach (var lineCount in new[] { 5000, 5001 })
        {
            var fixture = new RuleFixture();
            fixture.Files[Document] = string.Join(newline, Enumerable.Repeat(string.Empty, lineCount - 1).Append("end"))
                + (trailingTerminator ? newline : string.Empty);
            fixture.Changes.Add(Document);

            var diagnostics = RuleCatalog.Default.EvaluateDeltaSingle(CapacityRule, fixture.Build()).Diagnostics;

            Assert.Equal(lineCount > 5000, diagnostics.Any());
        }
    }

    [Theory]
    [InlineData("docs/develop/theory/Subvolume/Fixture.md", true)]
    [InlineData("docs/develop/theory/Fixture.MD", true)]
    [InlineData("docs/develop/theory/Fixture.md.txt", false)]
    [InlineData("docs/develop/theory/Fixture.json", false)]
    [InlineData("docs/develop/theory-other/Fixture.md", false)]
    [InlineData("docs/develop/spec/Fixture.md", false)]
    public void OnlyTheoryMarkdownIsSelected(string path, bool rejected)
    {
        var fixture = new RuleFixture();
        fixture.Files[path] = Lines(5001);
        fixture.Changes.Add(path);

        var diagnostics = RuleCatalog.Default.EvaluateDeltaSingle(CapacityRule, fixture.Build()).Diagnostics;

        Assert.Equal(rejected, diagnostics.Any());
    }

    [Fact]
    public void TheoryOnlyChangeActivatesDeltaPredicate()
    {
        var fixture = new RuleFixture();
        fixture.Files[Document] = Lines(5001);
        fixture.Changes.Clear();
        fixture.Changes.Add(Document);
        var context = fixture.Build();

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.ExecuteDelta(context));
        Assert.Contains(CapacityRule, completed.Capability.ExecutedRules);
        Assert.Contains(completed.Capability.Diagnostics,
            diagnostic => diagnostic.RuleId == CapacityRule && diagnostic.Path == Document
                && diagnostic.AdmissionEffect == AdmissionEffect.Block);
    }

    [Fact]
    public void UntouchedLongVolumeRemainsOutsideScopeEvenWhenJudgeChanges()
    {
        var fixture = new RuleFixture();
        fixture.Files[Document] = fixture.Baseline[Document] = Lines(6000);
        fixture.Changes.Clear();
        fixture.Changes.Add("tools/StrataLint.Engine/Rules/FutureRule.cs");
        var context = fixture.Build();

        Assert.True(context.RuleImplementationChanged);
        Assert.Empty(RuleCatalog.Default.EvaluateSingle(CapacityRule, context).Diagnostics);
        Assert.Empty(RuleCatalog.Default.EvaluateCurrentSingle(CapacityRule, context.CurrentFacts).Diagnostics);
        Assert.Empty(RepositoryCapacityAudit.InspectFiles([(Document, fixture.Files[Document])]));
    }

    [Fact]
    public void DeletedLongVolumeHasNoCandidateBodyToCheck()
    {
        var fixture = new RuleFixture();
        fixture.Baseline[Document] = Lines(6000);
        fixture.Changes.Add(Document);

        Assert.Empty(RuleCatalog.Default.EvaluateSingle(CapacityRule, fixture.Build()).Diagnostics);
    }

    [Fact]
    public void RenamedLongVolumeIsCheckedAtItsNewPath()
    {
        var fixture = new RuleFixture();
        const string oldPath = "docs/develop/theory/Old.md";
        fixture.Baseline[oldPath] = Lines(6000);
        fixture.Files[Document] = fixture.Baseline[oldPath];
        fixture.Changes.Add(oldPath);
        fixture.Changes.Add(Document);

        var finding = Assert.Single(RuleCatalog.Default.EvaluateDeltaSingle(CapacityRule, fixture.Build()).Diagnostics);

        Assert.Equal(Document, finding.Path);
        Assert.Equal(AdmissionEffect.Block, finding.AdmissionEffect);
    }

    [Fact]
    public void UnchangedCopySourceIsNotAModifiedVolume()
    {
        var fixture = new RuleFixture();
        const string copyPath = "docs/develop/theory/Copy.md";
        fixture.Files[Document] = fixture.Baseline[Document] = Lines(6000);
        fixture.Files[copyPath] = Lines(5000);
        var changes = RawChangeSet.CreateWithKinds(
        [
            (Document, RawChangeKind.Copied),
            (copyPath, RawChangeKind.Added),
        ]);

        Assert.Empty(RuleCatalog.Default.EvaluateDeltaSingle(CapacityRule, fixture.Build(changes)).Diagnostics);
    }

    private static string Lines(int count) => string.Concat(Enumerable.Repeat("line\n", count));
}
