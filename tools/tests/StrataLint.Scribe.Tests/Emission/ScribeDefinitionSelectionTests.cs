using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeDefinitionSelectionTests
{
    [Fact]
    public void ScopedEmitWithEmptyManifestDoesNotLoadTheDocumentsAssembly()
    {
        using var root = new TemporaryRoot();
        Directory.CreateDirectory(root.Resolve("Blueprint"));
        File.WriteAllText(root.Resolve("global.json"), "{}\n");
        var error = new StringWriter();
        var exit = ScribeCli.Run(
            ["emit", "--paths-from", "-"],
            root.Path,
            new StringWriter(),
            error,
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>()),
            new StringReader(string.Empty));

        Assert.Equal(0, exit);
        Assert.Empty(error.ToString());
    }

    [Fact]
    public void ScopedCheckNamesMarkdownDriftAndScopedEmitLeavesAttestationAlone()
    {
        using var root = new TemporaryRoot();
        File.WriteAllText(root.Resolve("global.json"), "{}\n");
        const string path = "Blueprint/D5/S0/Test/Scoped.scribe.cs";
        File.WriteAllText(root.Resolve(path), """
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Scoped : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("Scoped"), Blocks(Paragraph(Text("content")))));
            }
            """);
        File.WriteAllText(root.Resolve("Blueprint/D5/S0/Test/Unselected.scribe.cs"), "class Unselected {}");
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>());
        var error = new StringWriter();

        Assert.Equal(0, ScribeEmitter.EmitPaths(root.Path, [path], false, TextWriter.Null, error, report));
        Assert.False(File.Exists(root.Resolve("Evidence/Scribe/emission.json")));
        File.WriteAllText(root.Resolve("Blueprint/D5/S0/Test/Scoped.md"), "drift\n");
        error.GetStringBuilder().Clear();

        Assert.Equal(1, ScribeEmitter.EmitPaths(root.Path, [path], true, TextWriter.Null, error, report));
        Assert.Contains("Blueprint/D5/S0/Test/Scoped.md", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void ScopedEmitWithNonEmptyManifestDoesNotLoadTheDocumentsAssembly()
    {
        using var root = new TemporaryRoot();
        File.WriteAllText(root.Resolve("global.json"), "{}\n");
        const string path = "Blueprint/D5/S0/Test/NonEmpty.scribe.cs";
        File.WriteAllText(root.Resolve(path), """
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class NonEmpty : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("NonEmpty"), Blocks(Paragraph(Text("content")))));
            }
            """);
        var error = new StringWriter();
        var exit = ScribeCli.Run(
            ["emit", "--paths-from", "-"],
            root.Path,
            TextWriter.Null,
            error,
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>()),
            new StringReader(path));

        Assert.Equal(0, exit);
        Assert.Empty(error.ToString());
    }

    [Fact]
    public void EmptyChangesSelectNothing()
    {
        using var root = new TemporaryRoot();
        Add(root, "Blueprint/D5/S0/Test/First.scribe.cs", "class First {}");
        Assert.Empty(ScribeDefinitionSelector.Select(root.Path, []).Paths);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EmitRejectsCrossDocumentDescribeReferenceInFullAndScopedModes(bool scoped)
    {
        using var root = new TemporaryRoot();
        const string source = "Blueprint/D5/S0/Test/Source.scribe.cs";
        Add(root, source, """
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Source : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("Source"), Blocks(Paragraph(Text("body"))),
                        [DocumentEdge.NarrativeReference.ToDescribe(
                            GidRef.Create("D5/S0/Test/Target"), DescribeId.Create("target"))]));
            }
            """);
        const string target = "Blueprint/D5/S0/Test/Target.scribe.cs";
        Add(root, target, """
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Target : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("Target"), Blocks(Describe.Remark(
                        DescribeId.Create("target"), H("Target"), Num(1),
                        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("body")))))));
            }
            """);
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>());
        var error = new StringWriter();
        int exit;
        if (scoped)
        {
            exit = ScribeEmitter.EmitPaths(root.Path, [source], false, TextWriter.Null, error, report);
        }
        else
        {
            var results = ScribeScriptHost.ExecuteBatch(root.Path, [source, target]);
            Assert.All(results, result => Assert.True(result.IsSuccess, result.Failure?.ToString()));
            exit = ScribeEmitter.Emit(root.Path, false, TextWriter.Null, error, report,
                results.Select(result => result.Definition!).ToArray());
        }

        Assert.Equal(1, exit);
        Assert.Contains("code=cross-document-describe-reference path=D5/S0/Test/Source",
            error.ToString(), StringComparison.Ordinal);
        Assert.False(File.Exists(root.Resolve("Blueprint/D5/S0/Test/Source.md")));
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void EmitRejectsDanglingSelfDescribeReferenceInFullAndScopedModes(bool scoped, bool check)
    {
        using var root = new TemporaryRoot();
        File.WriteAllText(root.Resolve("global.json"), "{}\n");
        const string path = "Blueprint/D5/S0/Test/Local.scribe.cs";
        Add(root, path, """
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Local : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("Local"), Blocks(Describe.Remark(
                        DescribeId.Create("target"), H("Target"), Num(1),
                        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("body"))))),
                        [DocumentEdge.NarrativeReference.ToDescribe(
                            GidRef.Create("D5/S0/Test/Local"), DescribeId.Create("targte"))]));
            }
            """);
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>());
        var error = new StringWriter();
        int exit;
        if (scoped)
        {
            exit = ScribeCli.Run(
                check ? ["emit", "--paths-from", "-", "--check"] : ["emit", "--paths-from", "-"],
                root.Path, TextWriter.Null, error, report, new StringReader(path));
        }
        else
        {
            var result = ScribeScriptHost.Execute(root.Path, path);
            Assert.True(result.IsSuccess, result.Failure?.ToString());
            exit = ScribeEmitter.Emit(root.Path, check, TextWriter.Null, error, report,
                [result.Definition!]);
        }

        Assert.Equal(1, exit);
        Assert.Contains("code=dangling-describe-edge path=D5/S0/Test/Local",
            error.ToString(), StringComparison.Ordinal);
        Assert.Contains("D5/S0/Test/Local#describe/targte", error.ToString(), StringComparison.Ordinal);
        Assert.False(File.Exists(root.Resolve("Blueprint/D5/S0/Test/Local.md")));
    }

    [Fact]
    public void ScriptSelfDescribeReferencePreservesFullEmissionBytesInScopedEmitAndCheck()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Local.scribe.cs";
        Add(root, path, """
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Local : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("Local"), Blocks(Describe.Remark(
                        DescribeId.Create("target"), H("Target"), Num(1),
                        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("body"))))),
                        [DocumentEdge.NarrativeReference.ToDescribe(
                            GidRef.Create("D5/S0/Test/Local"), DescribeId.Create("target"))]));
            }
            """);
        var result = ScribeScriptHost.Execute(root.Path, path);
        Assert.True(result.IsSuccess, result.Failure?.ToString());
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>());
        var error = new StringWriter();

        Assert.Equal(0, ScribeEmitter.Emit(root.Path, false, TextWriter.Null, error, report,
            [result.Definition!]));
        var bytes = File.ReadAllBytes(root.Resolve("Blueprint/D5/S0/Test/Local.md"));
        Assert.Contains("<a id=\"describe-target\"></a>",
            System.Text.Encoding.UTF8.GetString(bytes), StringComparison.Ordinal);
        Assert.Equal(0, ScribeEmitter.Emit(root.Path, true, TextWriter.Null, error, report,
            [result.Definition!]));
        File.Delete(root.Resolve("Blueprint/D5/S0/Test/Local.md"));
        Assert.Equal(0, ScribeEmitter.EmitPaths(root.Path, [path], false, TextWriter.Null, error, report));
        Assert.Equal(bytes, File.ReadAllBytes(root.Resolve("Blueprint/D5/S0/Test/Local.md")));
        Assert.Equal(0, ScribeEmitter.EmitPaths(root.Path, [path], true, TextWriter.Null, error, report));
        Assert.Empty(error.ToString());
        Assert.Equal(bytes, File.ReadAllBytes(root.Resolve("Blueprint/D5/S0/Test/Local.md")));
    }

    [Theory]
    [InlineData("docs/unrelated.md")]
    [InlineData("Blueprint/D5/S0/Test/Deleted.scribe.cs")]
    public void NonEmptyManifestWithEmptySelectionDoesNotReadLeanReport(string path)
    {
        using var root = new TemporaryRoot();
        Directory.CreateDirectory(root.Resolve("Blueprint"));
        File.WriteAllText(root.Resolve("global.json"), "{}\n");
        var error = new StringWriter();
        var output = new StringWriter();

        var exit = ScribeCli.Run(
            ["emit", "--paths-from", "-", "--check"],
            root.Path, output, error, leanReport: null, new StringReader(path));

        Assert.Equal(0, exit);
        Assert.Empty(error.ToString());
        Assert.Contains("emitted: 0 changed blueprint(s)", output.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void MissingManifestReturnsTwoWithoutLoadingDocuments()
    {
        using var root = new TemporaryRoot();
        Directory.CreateDirectory(root.Resolve("Blueprint"));
        File.WriteAllText(root.Resolve("global.json"), "{}\n");
        var error = new StringWriter();

        var exit = ScribeCli.Run(
            ["emit", "--paths-from", "missing.paths"],
            root.Path,
            TextWriter.Null,
            error,
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>()));

        Assert.Equal(2, exit);
        Assert.NotEmpty(error.ToString());
    }

    [Fact]
    public void ChangedDefinitionSelectionIgnoresUnrelatedDefinitions()
    {
        using var root = new TemporaryRoot();
        Add(root, "Blueprint/D5/S0/Test/First.scribe.cs", "class First {}");
        Add(root, "Blueprint/D5/S0/Test/Second.scribe.cs", "class Second {}");

        var selected = ScribeDefinitionSelector.Select(
            root.Path,
            ["Blueprint/D5/S0/Test/First.scribe.cs"]);
        Assert.Single(selected.Paths);
        Assert.Equal("Blueprint/D5/S0/Test/First.scribe.cs", selected.Paths[0]);

        Add(root, "Blueprint/D5/S0/Test/Third.scribe.cs", "class Third {}");
        var afterUnrelatedAddition = ScribeDefinitionSelector.Select(
            root.Path,
            ["Blueprint/D5/S0/Test/First.scribe.cs"]);
        Assert.Equal(selected.Paths.ToArray(), afterUnrelatedAddition.Paths.ToArray());
    }

    [Fact]
    public void ChangedDefinitionSelectsOnlyItself()
    {
        using var root = new TemporaryRoot();
        const string changed = "Blueprint/D5/S0/Test/Changed.scribe.cs";
        Add(root, changed, "class Changed {}");
        Add(root, "Blueprint/D5/S0/Test/Mentions.scribe.cs", $"[ScribeSharedSource(\"{changed}\")] class Mentions {{}}");

        var selected = ScribeDefinitionSelector.Select(root.Path, [changed]);

        Assert.Equal(new[] { changed }, selected.Paths.ToArray());
    }

    [Fact]
    public void LeanAndProjectionInputsMapToDefinitionSources()
    {
        using var root = new TemporaryRoot();
        Add(root, "Blueprint/D5/S0/Test/First.scribe.cs", "class First {}");
        Add(root, "Golden/Projection/changed.json", "{\"declarations\":[{\"source_path\":\"D5/S0/Test/First.lean\"}]}");

        var selected = ScribeDefinitionSelector.Select(root.Path,
            ["D5/S0/Test/First.lean", "Golden/Projection/changed.json"]);
        Assert.Single(selected.Paths);
        Assert.Equal("Blueprint/D5/S0/Test/First.scribe.cs", selected.Paths[0]);
    }

    [Fact]
    public void DeletedDefinitionLeavesItsMarkdownProjectionUntouched()
    {
        using var root = new TemporaryRoot();
        File.WriteAllText(root.Resolve("global.json"), "{}\n");
        const string markdown = "Blueprint/D5/S0/Test/Deleted.md";
        File.WriteAllText(root.Resolve(markdown), "retained\n");
        var error = new StringWriter();

        var exit = ScribeEmitter.EmitPaths(
            root.Path,
            ["Blueprint/D5/S0/Test/Deleted.scribe.cs"],
            check: false,
            TextWriter.Null,
            error,
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>()));

        Assert.Equal(0, exit);
        Assert.Empty(error.ToString());
        Assert.Equal("retained\n", File.ReadAllText(root.Resolve(markdown)));
    }

    private static void Add(TemporaryRoot root, string path, string text) =>
        File.WriteAllText(root.Resolve(path), text);
}
