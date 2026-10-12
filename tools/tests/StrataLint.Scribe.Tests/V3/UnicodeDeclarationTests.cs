using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class UnicodeDeclarationTests
{
    private const string Module = "D5/S1/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction";
    private const string SourcePath = "Blueprint/" + Module + ".scribe.cs";

    [Theory]
    [InlineData("Bα")]
    [InlineData("Mα")]
    public void Synthetic_unicode_handles_preserve_the_exact_selector_and_resolve(string name)
    {
        var value = Module + "." + name;
        var reference = GidRef.Create(value);
        var handle = DeclarationHandle.Create(value);
        var compiledName = Module.Replace('/', '.') + "." + name;
        var catalog = Catalog(compiledName);

        Assert.Equal(value, reference.Value);
        Assert.Equal(value, handle.Value);
        Assert.Equal(Module + ".lean", reference.Path.Value);
        Assert.Equal(name, LeanDeclarationRef.Create(value).DeclarationName);
        var resolved = catalog.Resolve(handle);
        Assert.Equal(compiledName, resolved.Declaration.Name, StringComparer.Ordinal);
        Assert.Equal(LeanDeclarationKind.Definition, resolved.FormalKind);
    }

    [Theory]
    [InlineData("Bα")]
    [InlineData("Mα")]
    public void Unicode_catalog_selection_still_rejects_missing_and_ambiguous_names(string name)
    {
        var handle = DeclarationHandle.Create(Module + "." + name);

        Assert.Throws<InvalidOperationException>(() => Catalog().Resolve(handle));
        Assert.Throws<InvalidOperationException>(() => Catalog("One." + name, "Two." + name).Resolve(handle));
        Assert.Throws<InvalidOperationException>(() => Catalog(name, name).Resolve(handle));
    }

    [Theory]
    [InlineData("Bα", "BΑ")]
    [InlineData("Bα", "bα")]
    [InlineData("Bα", "Balpha")]
    [InlineData("Mα", "Malpha")]
    [InlineData("é", "e\u0301")]
    public void Catalog_matches_unicode_names_by_ordinal_equality(string selector, string otherName)
    {
        var handle = DeclarationHandle.Create(Module + "." + selector);
        Assert.Throws<InvalidOperationException>(() => Catalog("Namespace." + otherName).Resolve(handle));
        var resolved = Catalog("Namespace." + selector, "Namespace." + otherName).Resolve(handle);
        Assert.Equal("Namespace." + selector, resolved.Declaration.Name);
    }

    [Theory]
    [InlineData("D5/S1/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction")]
    [InlineData("D5/B/S1/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction")]
    [InlineData("D5/E/S1/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.result--json")]
    [InlineData("D5/S1/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.Bα.extra")]
    [InlineData("D5/S1/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.2α")]
    [InlineData("D5/S1/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.Bα--json")]
    [InlineData("D5/S1/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.Bα\u200b")]
    public void Declaration_handle_keeps_its_formal_declaration_boundary(string value)
    {
        Assert.Throws<ArgumentException>(() => DeclarationHandle.Create(value));
    }

    [Fact]
    public void Script_host_executes_and_renders_unicode_describe_nodes_against_the_catalog()
    {
        using var root = new StatementProjectionTestRepository();
        var scriptPath = Path.Combine(root.Path, SourcePath);
        Directory.CreateDirectory(Path.GetDirectoryName(scriptPath)!);
        File.WriteAllText(scriptPath, $$"""
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            using static StrataLint.Scribe.FormulaDsl;

            internal sealed class UnicodeDefinitions : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("Definitions"), Blocks(
                        Describe.Lean(DescribeId.Create("b"), DeclarationHandle.Create("{{Module}}.Bα"),
                            H("Damped matrix"), StatementSource.FromAuthor(Disp(D(1))), AssessedProvenance.FromRepo(),
                            Blocks(Paragraph(Text("Matrix definition.")))),
                        Describe.Lean(DescribeId.Create("m"), DeclarationHandle.Create("{{Module}}.Mα"),
                            H("Transfer map"), StatementSource.FromAuthor(Disp(D(1))), AssessedProvenance.FromRepo(),
                            Blocks(Paragraph(Text("Map definition.")))))));
            }
            """);

        var execution = ScribeScriptHost.Execute(root.Path, SourcePath);
        Assert.True(execution.IsSuccess, execution.Failure?.ToString());
        var document = execution.Definition!.Document;
        var catalog = Catalog("Namespace.Bα", "Namespace.Mα");
        var descriptions = document.Content.Items.Cast<DocumentBlock.Describe>().ToArray();
        Assert.Equal(2, descriptions.Length);
        foreach (var describe in descriptions)
        {
            var statement = Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);
            var resolved = catalog.Resolve(DeclarationHandle.Create(statement.Value.Value));
            Assert.Equal("Namespace." + statement.Value.DeclarationName, resolved.Declaration.Name);
            Assert.Equal(DescribeKind.Definition, catalog.ResolveKind(describe));
        }
        var markdown = System.Text.Encoding.UTF8.GetString(CanonicalMarkdownWriter.Write(document, catalog).AsSpan());
        Assert.Contains(Module + ".Bα", markdown, StringComparison.Ordinal);
        Assert.Contains(Module + ".Mα", markdown, StringComparison.Ordinal);
    }

    private static DeclarationCatalog Catalog(params string[] names) =>
        DeclarationCatalog.Create(LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                [Module + ".lean"] = new([], names.Select(static name =>
                    new LeanDeclaration(name, "def", "Nat", [])).ToImmutableArray()),
            }));
}
