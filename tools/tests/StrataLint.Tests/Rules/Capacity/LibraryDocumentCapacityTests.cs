using StrataLint.Engine;
using StrataLint.TestSupport;

namespace StrataLint.Tests;

public sealed class LibraryDocumentCapacityTests
{
    private const string Document = "Library/notes/fixture.md";
    private static readonly RuleId CapacityRule = RuleId.CreateKnown(3);

    [Theory]
    [InlineData(RawChangeKind.Added, 0, false)]
    [InlineData(RawChangeKind.Added, 3000, false)]
    [InlineData(RawChangeKind.Added, 3001, true)]
    [InlineData(RawChangeKind.Modified, 0, false)]
    [InlineData(RawChangeKind.Modified, 3000, false)]
    [InlineData(RawChangeKind.Modified, 3001, true)]
    public void ChangedNoteUsesItsOwnHardLimit(RawChangeKind kind, int lines, bool rejected)
    {
        var fixture = new RuleFixture();
        if (kind == RawChangeKind.Modified)
            fixture.Baseline[Document] = Lines(1);
        fixture.Files[Document] = Lines(lines);
        fixture.Changes.Add(Document);

        var diagnostics = RuleCatalog.Default.EvaluateSingle(CapacityRule, fixture.Build(
            RawChangeSet.CreateWithKinds([(Document, kind)]))).Diagnostics;

        if (!rejected)
        {
            Assert.Empty(diagnostics);
            return;
        }

        var finding = Assert.Single(diagnostics);
        Assert.Equal(Document, finding.Path);
        Assert.Equal(AdmissionEffect.Block, finding.AdmissionEffect);
        Assert.Contains("3001 lines (hard limit 3000)", finding.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("\n", true)]
    [InlineData("\n", false)]
    [InlineData("\r\n", true)]
    [InlineData("\r\n", false)]
    public void BlankLinesCountAndTrailingTerminatorDoesNotAddALine(string newline, bool trailingTerminator)
    {
        foreach (var lineCount in new[] { 3000, 3001 })
        {
            var fixture = new RuleFixture();
            fixture.Files[Document] = string.Join(newline, Enumerable.Repeat(string.Empty, lineCount - 1).Append("文献"))
                + (trailingTerminator ? newline : string.Empty);
            fixture.Changes.Add(Document);

            var diagnostics = RuleCatalog.Default.EvaluateDeltaSingle(CapacityRule, fixture.Build(
                RawChangeSet.CreateWithKinds([(Document, RawChangeKind.Added)]))).Diagnostics;

            Assert.Equal(lineCount > 3000, diagnostics.Any());
        }
    }

    [Theory]
    [InlineData("Library/Arith/fixture.md", true)]
    [InlineData("Library/Arith/Subdomain/fixture.md", true)]
    [InlineData("Library/notes/fixture.MD", true)]
    [InlineData("Library/notes/fixture.md.txt", false)]
    [InlineData("Library/queries.yaml", false)]
    [InlineData("Library-other/fixture.md", false)]
    [InlineData("docs/develop/theory/Fixture.md", false)]
    public void OnlyLibraryMarkdownIsSelected(string path, bool rejected)
    {
        var fixture = new RuleFixture();
        fixture.Files[path] = Lines(3001);
        fixture.Changes.Add(path);

        var diagnostics = RuleCatalog.Default.EvaluateDeltaSingle(CapacityRule, fixture.Build(
            RawChangeSet.CreateWithKinds([(path, RawChangeKind.Added)]))).Diagnostics;

        Assert.Equal(rejected, diagnostics.Any());
    }

    [Theory]
    [InlineData(2999, 3000, false)]
    [InlineData(3000, 3001, true)]
    [InlineData(6000, 6001, true)]
    [InlineData(6000, 6000, true)]
    [InlineData(6000, 5000, true)]
    [InlineData(6000, 3000, false)]
    public void ModifiedNoteChecksFullCandidateRegardlessOfBaseline(int baselineLines, int candidateLines, bool rejected)
    {
        var fixture = new RuleFixture();
        fixture.Baseline[Document] = Lines(baselineLines);
        fixture.Files[Document] = Lines(candidateLines).Replace("line", "changed", StringComparison.Ordinal);
        fixture.Changes.Add(Document);

        var diagnostics = RuleCatalog.Default.EvaluateDeltaSingle(CapacityRule, fixture.Build()).Diagnostics;

        if (!rejected)
        {
            Assert.Empty(diagnostics);
            return;
        }

        var finding = Assert.Single(diagnostics);
        Assert.Equal(Document, finding.Path);
        Assert.Equal(AdmissionEffect.Block, finding.AdmissionEffect);
        Assert.Contains($"{candidateLines} lines (hard limit 3000)", finding.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(RawChangeKind.Added)]
    [InlineData(RawChangeKind.Modified)]
    public void LibraryOnlyChangeActivatesDeltaPredicate(RawChangeKind kind)
    {
        var fixture = new RuleFixture();
        if (kind == RawChangeKind.Modified)
            fixture.Baseline[Document] = Lines(3000);
        fixture.Files[Document] = Lines(3001);
        fixture.Changes.Clear();
        fixture.Changes.Add(Document);

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.ExecuteDelta(fixture.Build(
            RawChangeSet.CreateWithKinds([(Document, kind)]))));

        Assert.Contains(CapacityRule, completed.Capability.ExecutedRules);
        Assert.Contains(completed.Capability.Diagnostics,
            diagnostic => diagnostic.RuleId == CapacityRule && diagnostic.Path == Document
                && diagnostic.AdmissionEffect == AdmissionEffect.Block);
    }

    [Fact]
    public void UntouchedLongNoteRemainsOutsideScopeEvenWhenJudgeChanges()
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
    public void DeletedLongNoteHasNoCandidateBodyToCheck()
    {
        var fixture = new RuleFixture();
        fixture.Baseline[Document] = Lines(6000);
        fixture.Changes.Add(Document);

        Assert.Empty(RuleCatalog.Default.EvaluateSingle(CapacityRule, fixture.Build(
            RawChangeSet.CreateWithKinds([(Document, RawChangeKind.Deleted)]))).Diagnostics);
    }

    [Theory]
    [InlineData(RawChangeKind.Deleted)]
    [InlineData(RawChangeKind.Copied)]
    public void RenameAndCopyDestinationsAreCheckedAtTheirNewPath(RawChangeKind sourceKind)
    {
        var fixture = new RuleFixture();
        const string oldPath = "Library/notes/old.md";
        fixture.Baseline[oldPath] = Lines(6000);
        if (sourceKind == RawChangeKind.Copied)
            fixture.Files[oldPath] = fixture.Baseline[oldPath];
        fixture.Files[Document] = fixture.Baseline[oldPath];
        var changes = RawChangeSet.CreateWithKinds(
        [
            (oldPath, sourceKind),
            (Document, RawChangeKind.Added),
        ]);

        var finding = Assert.Single(RuleCatalog.Default.EvaluateDeltaSingle(CapacityRule, fixture.Build(changes)).Diagnostics);

        Assert.Equal(Document, finding.Path);
        Assert.Equal(AdmissionEffect.Block, finding.AdmissionEffect);
    }

    [Fact]
    public void LibraryNotesStillCountTowardDirectoryCapacity()
    {
        var files = Enumerable.Range(0, RepositoryRules.DirectoryToleranceLimit + 1)
            .Select(index => ($"Library/notes/note{index}.md", Lines(3000)));

        var finding = Assert.Single(RepositoryCapacityAudit.InspectFiles(files));

        Assert.Equal("Library/notes", finding.Path);
        Assert.Contains("directory contains", finding.Message, StringComparison.Ordinal);
    }

    private static string Lines(int count) => string.Concat(Enumerable.Repeat("line\n", count));
}
