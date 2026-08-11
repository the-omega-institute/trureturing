using System.Collections.Immutable;
using System.Reflection;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests.V3;

public sealed class ReportDerivedDeclarationTests
{
    [Fact]
    public void DeclarationHandle_is_a_value_with_one_public_governed_factory()
    {
        Assert.True(typeof(DeclarationHandle).IsValueType);
        var factories = typeof(DeclarationHandle).GetMethods(BindingFlags.Public | BindingFlags.Static)
            .Where(static method => method.ReturnType == typeof(DeclarationHandle))
            .ToArray();
        var factory = Assert.Single(factories);
        Assert.Equal(nameof(DeclarationHandle.Create), factory.Name);
        Assert.Equal([typeof(string)], factory.GetParameters().Select(static parameter => parameter.ParameterType));
    }

    [Fact]
    public void Catalog_fails_closed_when_exact_declaration_is_missing()
    {
        var missing = DeclarationCatalog.Create(Report());
        Assert.Throws<InvalidOperationException>(() => missing.Resolve(DeclarationHandle.Create(Gid)));
    }

    [Fact]
    public void Catalog_fails_closed_when_exact_declaration_is_ambiguous()
    {
        var ambiguous = DeclarationCatalog.Create(Report(
            Declaration(CanonicalName, "theorem"),
            Declaration(CanonicalName, "theorem")));
        Assert.Throws<InvalidOperationException>(() => ambiguous.Resolve(DeclarationHandle.Create(Gid)));
    }

    [Fact]
    public void Catalog_rejects_two_different_full_names_with_the_same_suffix()
    {
        var catalog = DeclarationCatalog.Create(Report(
            Declaration("One.claim", "theorem"),
            Declaration("Two.claim", "theorem")));
        Assert.Throws<InvalidOperationException>(() => catalog.Resolve(DeclarationHandle.Create(Gid)));
    }

    [Fact]
    public void Catalog_fails_closed_for_malformed_declaration_kind()
    {
        Assert.Throws<InvalidOperationException>(() => DeclarationCatalog.Create(Report(
            Declaration("claim", "unknown-kind"))));
    }

    [Fact]
    public void Catalog_fails_closed_for_sorry_declaration()
    {
        var sorry = DeclarationCatalog.Create(Report(new LeanDeclaration(
            CanonicalName, "theorem", "Nat = Nat", ImmutableArray.Create("sorryAx"))));
        Assert.Throws<InvalidOperationException>(() => sorry.Resolve(DeclarationHandle.Create(Gid)));
    }

    [Fact]
    public void DeclarationHandle_rejects_non_gid_input()
    {
        Assert.Throws<ArgumentException>(() => DeclarationHandle.Create("not-a-gid"));
    }

    [Fact]
    public void Catalog_derives_kind_and_sorry_status_from_the_report()
    {
        var catalog = DeclarationCatalog.Create(Report(Declaration(CanonicalName, "def")));

        var resolved = catalog.Resolve(DeclarationHandle.Create(Gid));

        Assert.Equal(DescribeKind.Definition, resolved.Kind);
        Assert.Equal(LeanDeclarationKind.Definition, resolved.FormalKind);
        Assert.True(resolved.IsSorryFree);
        Assert.Equal("def", resolved.Declaration.Kind);
    }

    [Theory]
    [InlineData("axiom", LeanDeclarationKind.Axiom)]
    [InlineData("def", LeanDeclarationKind.Definition)]
    [InlineData("theorem", LeanDeclarationKind.Theorem)]
    [InlineData("opaque", LeanDeclarationKind.Opaque)]
    [InlineData("quotient", LeanDeclarationKind.Quotient)]
    [InlineData("constructor", LeanDeclarationKind.Constructor)]
    [InlineData("recursor", LeanDeclarationKind.Recursor)]
    [InlineData("inductive", LeanDeclarationKind.Inductive)]
    public void Catalog_resolves_every_legal_report_kind(
        string reportKind,
        LeanDeclarationKind expectedKind)
    {
        var catalog = DeclarationCatalog.Create(Report(Declaration(CanonicalName, reportKind)));

        var resolved = catalog.Resolve(DeclarationHandle.Create(Gid));

        Assert.Equal(expectedKind, resolved.FormalKind);
    }

    [Fact]
    public void Describe_selection_rejects_a_legal_nonprojectable_kind_explicitly()
    {
        var catalog = DeclarationCatalog.Create(Report(Declaration(CanonicalName, "inductive")));
        var describe = Describe.Lean(
            DescribeId.Create("claim"),
            DeclarationHandle.Create(Gid),
            DefinitionDsl.H("Claim"),
            new AssessedProvenance.RepoDerived(),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Narrative"))));

        var error = Assert.Throws<InvalidOperationException>(() => catalog.ResolveKind(describe));

        Assert.Contains("cannot be projected to a Describe kind", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("unsupported kind", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ScribeNode_derives_the_same_gid_as_legacy_header()
    {
        const string path = "/repo/Blueprint/D5/S0/Computability/SemanticLayerShift.scribe.cs";
        var oldHeader = DefinitionDsl.Header(
            "D5/S0/Computability/SemanticLayerShift",
            "Digest");

        var document = ScribeNode.Create(
            "Digest",
            DefinitionDsl.H("Title"),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Content"))),
            sourcePath: path);

        Assert.Equal(oldHeader.Gid, document.Header.Gid);
    }

    [Fact]
    public void Lean_describe_signature_has_no_repeated_formal_fields()
    {
        var method = typeof(Describe).GetMethod(nameof(Describe.Lean), BindingFlags.Public | BindingFlags.Static);
        Assert.NotNull(method);
        Assert.Equal(
            [typeof(DescribeId), typeof(DeclarationHandle), typeof(Heading),
             typeof(AssessedProvenance), typeof(BlockSequence), typeof(DescribeRole?)],
            method!.GetParameters().Select(static parameter => parameter.ParameterType));
        Assert.DoesNotContain(method.GetParameters(), static parameter =>
            parameter.ParameterType == typeof(LeanDeclarationKind)
            || parameter.ParameterType == typeof(Formula)
            || parameter.ParameterType == typeof(bool));
    }

    [Fact]
    public void Novel_after_search_receipt_survives_in_the_describe_ast()
    {
        var receipt = GidRef.Create("D5/S0/Computability/SemanticLayerShift");
        var describe = Describe.Lean(
            DescribeId.Create("claim"), DeclarationHandle.Create(Gid),
            DefinitionDsl.H("Claim"), AssessedProvenance.NovelAfterSearch(receipt),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Narrative"))));

        var assessed = Assert.IsType<AssessedProvenance.SuspectedNovel>(describe.AssessedProvenance);
        Assert.Equal(receipt, assessed.SearchReceipt);
    }

    [Fact]
    public void Writers_accept_a_catalog_but_never_a_lean_report()
    {
        foreach (var writer in new[] { typeof(CanonicalMarkdownWriter), typeof(QuestPdfWriter) })
        {
            var write = Assert.Single(writer.GetMethods(BindingFlags.Public | BindingFlags.Static));
            var parameters = write.GetParameters().Select(static parameter => parameter.ParameterType).ToArray();
            Assert.Contains(typeof(DeclarationCatalog), parameters);
            Assert.DoesNotContain(typeof(LeanAxiomReport), parameters);
        }
    }

    [Fact]
    public void Migrated_joint_coordinates_markdown_matches_frozen_utf8_bytes()
    {
        var root = FindRepositoryRoot();
        var definitions = DocumentDefinitions.Discover(typeof(DocumentDefinitions).Assembly, root);
        var migrated = definitions
            .Single(definition => definition.Document.Header.Gid.Value ==
                "D5/S1/Depth/JointCoordinates").Document;
        var migratedDescribe = Assert.IsType<DocumentBlock.Describe>(Assert.Single(migrated.Content.Items));
        Assert.IsType<AssessedProvenance.RepoDerived>(migratedDescribe.AssessedProvenance);
        var documents = definitions.Select(static definition => definition.Document).ToArray();
        var declaration = new LeanDeclaration(
            "D5.S1.Depth.JointCoordinates.joint_coordinates_spec",
            "theorem",
            "statement-v1(source=D5.S1.Depth.JointCoordinates.joint_coordinates_spec)",
            ImmutableArray.Create("propext", "Classical.choice", "Quot.sound"));
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            ["D5/S1/Depth/JointCoordinates.lean"] = new(
                ImmutableArray.Create("D5.S1.Phase.Basic", "D5.S1.Scale.Log"),
                ImmutableArray.Create(declaration)),
        });
        var catalog = DeclarationCatalog.Create(report);
        var census = ReceiptFreeDocumentCatalog.Load(root, documents);
        var graph = DocumentGraphAssembler.Assemble(
            documents, report, census.ReceiptFreeDocumentGids);

        var expected = File.ReadAllBytes(Path.Combine(
            AppContext.BaseDirectory, "Fixtures", "JointCoordinates.before-migration.md"));
        var actual = CanonicalMarkdownWriter.Write(
            migrated, catalog, graph: graph).ToArray();
        Assert.True(
            expected.AsSpan().SequenceEqual(actual),
            Encoding.UTF8.GetString(actual));
    }

    private const string Gid = "D5/S0/Computability/SemanticLayerShift.claim";
    private const string CanonicalName = "D5.S0.Computability.SemanticLayerShift.claim";

    private static LeanDeclaration Declaration(string name, string kind) =>
        new(name, kind, "Nat = Nat", ImmutableArray<string>.Empty);

    private static LeanAxiomReport Report(params LeanDeclaration[] declarations) =>
        LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [declarations.Any(static declaration => declaration.Name.Contains("JointCoordinates", StringComparison.Ordinal))
                ? "D5/S1/Depth/JointCoordinates.lean"
                : "D5/S0/Computability/SemanticLayerShift.lean"] = new(
                ImmutableArray<string>.Empty,
                declarations.ToImmutableArray()),
        });

    private static string FindRepositoryRoot()
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null && !Directory.Exists(Path.Combine(directory.FullName, "Blueprint")))
        {
            directory = directory.Parent;
        }
        return directory?.FullName
            ?? throw new InvalidOperationException("Repository root is unavailable.");
    }

}
