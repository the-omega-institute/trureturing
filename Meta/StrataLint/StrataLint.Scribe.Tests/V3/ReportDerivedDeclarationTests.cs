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
    public void Catalog_fails_closed_for_missing_ambiguous_and_malformed_declarations()
    {
        var missing = DeclarationCatalog.Create(Report());
        Assert.Throws<InvalidOperationException>(() => missing.Resolve(DeclarationHandle.Create(Gid)));

        var ambiguous = DeclarationCatalog.Create(Report(
            Declaration("One.claim", "theorem"),
            Declaration("Two.claim", "theorem")));
        Assert.Throws<InvalidOperationException>(() => ambiguous.Resolve(DeclarationHandle.Create(Gid)));

        Assert.Throws<InvalidOperationException>(() => DeclarationCatalog.Create(Report(
            Declaration("claim", "unknown-kind"))));
        var sorry = DeclarationCatalog.Create(Report(new LeanDeclaration(
            "claim", "theorem", "Nat = Nat", ImmutableArray.Create("sorryAx"))));
        Assert.Throws<InvalidOperationException>(() => sorry.Resolve(DeclarationHandle.Create(Gid)));
        Assert.Throws<ArgumentException>(() => DeclarationHandle.Create("not-a-gid"));
    }

    [Fact]
    public void Catalog_derives_kind_and_sorry_status_from_the_report()
    {
        var catalog = DeclarationCatalog.Create(Report(Declaration("Namespace.claim", "def")));

        var resolved = catalog.Resolve(DeclarationHandle.Create(Gid));

        Assert.Equal(DescribeKind.Definition, resolved.Kind);
        Assert.Equal(LeanDeclarationKind.Definition, resolved.FormalKind);
        Assert.True(resolved.IsSorryFree);
        Assert.Equal("def", resolved.Declaration.Kind);
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
    public void Migrated_joint_coordinates_markdown_is_byte_identical_to_legacy_ast()
    {
        var root = FindRepositoryRoot();
        var migrated = DocumentDefinitions.Discover(typeof(DocumentDefinitions).Assembly, root)
            .Single(definition => definition.Document.Header.Gid.Value ==
                "D5/S1/Depth/JointCoordinates").Document;
        var migratedDescribe = Assert.IsType<DocumentBlock.Describe>(Assert.Single(migrated.Content.Items));
        var reference = LeanDeclarationRef.Create(
            "D5/S1/Depth/JointCoordinates.joint_coordinates_spec",
            expectedKind: LeanDeclarationKind.Theorem,
            requireNoSorry: true);
        var legacy = ScribeDocument.Create(
            DefinitionDsl.Header(migrated.Header.Gid.Value, migrated.Header.Digest.Value),
            migrated.Title,
            BlockSequence.Create([
                DocumentBlock.Describe.Definition(
                    migratedDescribe.Id,
                    migratedDescribe.Title,
                    reference,
                    DescribeProvenance.RepoDerived(),
                    migratedDescribe.Content),
            ]));
        var report = Report(new LeanDeclaration(
            "D5.S1.Depth.JointCoordinates.joint_coordinates_spec",
            "theorem",
            "statement-v1(source=D5.S1.Depth.JointCoordinates.joint_coordinates_spec)",
            ImmutableArray.Create("propext", "Classical.choice", "Quot.sound")));

        Assert.Equal(
            Encoding.UTF8.GetString(CanonicalMarkdownWriter.Write(legacy, report).AsSpan()),
            Encoding.UTF8.GetString(CanonicalMarkdownWriter.Write(migrated, report).AsSpan()));
    }

    private const string Gid = "D5/S0/Computability/SemanticLayerShift.claim";

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
