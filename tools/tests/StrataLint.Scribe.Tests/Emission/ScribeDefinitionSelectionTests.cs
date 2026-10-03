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
            () => throw new InvalidOperationException("documents assembly must not be loaded"),
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
            () => throw new InvalidOperationException("documents assembly must not be loaded"),
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

    [Fact]
    public void MissingManifestReturnsTwoWithoutLoadingDocuments()
    {
        using var root = new TemporaryRoot();
        Directory.CreateDirectory(root.Resolve("Blueprint"));
        File.WriteAllText(root.Resolve("global.json"), "{}\n");
        var error = new StringWriter();

        var exit = ScribeCli.Run(
            () => throw new InvalidOperationException("documents assembly must not be loaded"),
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
    public void SharedSourceSelectsItsUsers()
    {
        using var root = new TemporaryRoot();
        Add(root, "Blueprint/D5/S0/Test/First.scribe.cs", "[ScribeSharedSource(\"Blueprint/Shared.scribe.cs\")] class First {}");
        Add(root, "Blueprint/D5/S0/Test/Second.scribe.cs", "class Second {}");
        Add(root, "Blueprint/Shared.scribe.cs", "class Shared {}");

        var selected = ScribeDefinitionSelector.Select(root.Path, ["Blueprint/Shared.scribe.cs"]);
        Assert.True(selected.Paths.SequenceEqual(
            ["Blueprint/D5/S0/Test/First.scribe.cs", "Blueprint/Shared.scribe.cs"]));
    }

    [Fact]
    public void SharedSourceSelectionUsesTheHostSyntaxContract()
    {
        using var root = new TemporaryRoot();
        const string shared = "Blueprint/Shared.scribe.cs";
        Add(root, shared, "class Shared {}");
        Add(root, "Blueprint/D5/S0/Test/Simple.scribe.cs",
            $"[ScribeSharedSource(\"{shared}\")] class Simple {{}}");
        Add(root, "Blueprint/D5/S0/Test/Suffix.scribe.cs",
            $"[ScribeSharedSourceAttribute(\"{shared}\")] class Suffix {{}}");
        Add(root, "Blueprint/D5/S0/Test/Qualified.scribe.cs",
            $"[StrataLint.Scribe.ScribeSharedSource(\"{shared}\")] class Qualified {{}}");
        Add(root, "Blueprint/D5/S0/Test/Aliased.scribe.cs",
            $"[global::StrataLint.Scribe.ScribeSharedSource(\"{shared}\")] record Aliased {{}}");
        Add(root, "Blueprint/D5/S0/Test/Unrelated.scribe.cs", "class Unrelated {}");

        var selected = ScribeDefinitionSelector.Select(root.Path, [shared]);

        Assert.True(selected.Paths.SequenceEqual(
            [
                "Blueprint/D5/S0/Test/Aliased.scribe.cs",
                "Blueprint/D5/S0/Test/Qualified.scribe.cs",
                "Blueprint/D5/S0/Test/Simple.scribe.cs",
                "Blueprint/D5/S0/Test/Suffix.scribe.cs",
                "Blueprint/Shared.scribe.cs",
            ]));
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
