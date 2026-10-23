using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeLeanInputSelectionTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ScopedEmitChecksCurrentSourceOfUnimportedDeclarationReference(bool changed)
    {
        using var root = new TemporaryRoot(sdkConfiguration: true);
        File.WriteAllText(root.Resolve("global.json"), "{}\n");
        const string owner = "D5/S0/Test/Selected.lean";
        const string referenced = "D5/S0/Test/Referenced.lean";
        const string scribe = "Blueprint/D5/S0/Test/Selected.scribe.cs";
        const string markdown = "Blueprint/D5/S0/Test/Selected.md";
        var sources = new Dictionary<string, string>
        {
            [owner] = "prelude\n-- owner\n",
            [referenced] = "prelude\ntheorem result : True := True.intro\n",
        };
        foreach (var (path, source) in sources) File.WriteAllText(root.Resolve(path), source);
        File.WriteAllText(root.Resolve(scribe), """
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Selected : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("Selected"), Blocks(
                        Paragraph(Ref("D5/S0/Test/Referenced.result")))));
            }
            """);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(sources.Select(pair => RawRepositoryEntry.FromText(pair.Key, pair.Value))))).Snapshot;
        var reportPath = root.Resolve(".lake/build/stratalint/raw-lean-report.json");
        RawLeanReportArtifact.WriteFile(reportPath, snapshot, LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            [owner] = new([], []),
            [referenced] = new([], [new LeanDeclaration("result", "theorem", "True", [])]),
        }));
        File.WriteAllText(reportPath, File.ReadAllText(reportPath).Replace(
            RawLeanReportArtifact.Schema, RawLeanReportArtifact.ScopedSchema, StringComparison.Ordinal));
        if (changed) File.WriteAllText(root.Resolve(referenced), "prelude\ntheorem result : True ∧ True := ⟨True.intro, True.intro⟩\n");
        File.WriteAllText(root.Resolve(markdown), "previous emission\n");
        var error = new StringWriter();

        var exit = ScribeCli.Run(["emit", "--paths-from", "-", "--scoped"], root.Path,
            TextWriter.Null, error, leanReport: null, new StringReader(scribe));

        Assert.True((exit == 0) == !changed, error.ToString());
        if (changed)
        {
            Assert.Contains("source hash does not match " + referenced, error.ToString(), StringComparison.Ordinal);
            Assert.Equal("previous emission\n", File.ReadAllText(root.Resolve(markdown)));
        }
    }

    [Fact]
    public void LeanInputsComeFromSelectedTypedDocumentsAndTheirDeclarationReferences()
    {
        using var root = new TemporaryRoot(sdkConfiguration: true);
        File.WriteAllText(root.Resolve("global.json"), "{}\n");
        const string path = "Blueprint/D5/S0/Test/Selected.scribe.cs";
        File.WriteAllText(root.Resolve(path), """
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Selected : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("Selected"), Blocks(
                        Paragraph(Text("body"), Ref("D5/S0/Test/Referenced.result")))));
            }
            """);
        File.WriteAllText(root.Resolve("Blueprint/D5/S0/Test/Unselected.scribe.cs"), "invalid unselected source");
        var output = new StringWriter();
        var error = new StringWriter();

        var exit = ScribeCli.Run(["lean-inputs", "--paths-from", "-"], root.Path,
            output, error, new StringReader(path));

        Assert.True(exit == 0, error.ToString());
        Assert.Equal("D5.S0.Test.Referenced\nD5.S0.Test.Selected\n", output.ToString().Replace("\r\n", "\n", StringComparison.Ordinal));
        Assert.Empty(error.ToString());
        Assert.False(File.Exists(root.Resolve("Blueprint/D5/S0/Test/Selected.md")));
    }

    [Theory]
    [InlineData("")]
    [InlineData("docs/unrelated.md")]
    public void LeanInputsRejectEmptySelection(string paths)
    {
        using var root = new TemporaryRoot(sdkConfiguration: true);
        Directory.CreateDirectory(root.Resolve("Blueprint"));
        File.WriteAllText(root.Resolve("global.json"), "{}\n");

        Assert.NotEqual(0, ScribeCli.Run(["lean-inputs", "--paths-from", "-"], root.Path,
            TextWriter.Null, new StringWriter(), new StringReader(paths)));
    }

    [Theory]
    [InlineData("")]
    [InlineData("docs/unrelated.md")]
    public void ScopedEmitRejectsEmptyLeanScopeBeforeWriting(string paths)
    {
        using var root = new TemporaryRoot(sdkConfiguration: true);
        Directory.CreateDirectory(root.Resolve("Blueprint"));
        File.WriteAllText(root.Resolve("global.json"), "{}\n");
        var error = new StringWriter();

        var exit = ScribeCli.Run(["emit", "--paths-from", "-", "--scoped"], root.Path,
            TextWriter.Null, error, leanReport: null, new StringReader(paths));

        Assert.NotEqual(0, exit);
        Assert.Contains("scope is empty", error.ToString(), StringComparison.Ordinal);
        Assert.Empty(Directory.EnumerateFiles(root.Resolve("Blueprint"), "*.md", SearchOption.AllDirectories));
        Assert.False(Directory.Exists(root.Resolve(".lake")));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ScopedEmitConsumesOnlyItsIndependentlySelectedLeanInputs(bool implicitInit)
    {
        using var root = new TemporaryRoot(sdkConfiguration: true);
        File.WriteAllText(root.Resolve("global.json"), "{}\n");
        const string source = "D5/S0/Test/Selected.lean";
        const string path = "Blueprint/D5/S0/Test/Selected.scribe.cs";
        var sourceText = implicitInit ? "-- selected source\n" : "prelude\n-- selected source\n";
        File.WriteAllText(root.Resolve(source), sourceText);
        File.WriteAllText(root.Resolve("D5/S0/Test/Unselected.lean"), "-- unselected source\n");
        File.WriteAllText(root.Resolve(path), """
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Selected : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("Selected"), Blocks(Paragraph(Text("body")))));
            }
            """);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([RawRepositoryEntry.FromText(source, sourceText)]))).Snapshot;
        var reportPath = root.Resolve(".lake/build/stratalint/raw-lean-report.json");
        RawLeanReportArtifact.WriteFile(reportPath, snapshot,
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
            {
                [source] = new(implicitInit ? ["Init"] : [], []),
            }));
        File.WriteAllText(reportPath, File.ReadAllText(reportPath).Replace(
            "stratalint-raw-lean-report-v3", "stratalint-scoped-lean-report-v1", StringComparison.Ordinal));
        var error = new StringWriter();

        var exit = ScribeCli.Run(["emit", "--paths-from", "-", "--scoped"], root.Path,
            TextWriter.Null, error, leanReport: null, new StringReader(path));

        Assert.True(exit == 0, error.ToString());
        Assert.True(File.Exists(root.Resolve("Blueprint/D5/S0/Test/Selected.md")));
        Assert.False(File.Exists(root.Resolve("Blueprint/D5/S0/Test/Unselected.md")));
    }
}
