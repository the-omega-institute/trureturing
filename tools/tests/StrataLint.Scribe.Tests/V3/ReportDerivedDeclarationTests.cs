using System.Collections.Immutable;
using System.Reflection;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;
using static StrataLint.TestSupport.ReportDerivedDeclarationFixture;

namespace StrataLint.Scribe.Tests;

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
    public void Catalog_fails_closed_when_declaration_is_missing()
    {
        var missing = DeclarationCatalog.Create(Report());
        Assert.Throws<InvalidOperationException>(() => missing.Resolve(DeclarationHandle.Create(Gid)));
    }

    [Fact]
    public void Catalog_fails_closed_when_same_module_short_name_is_ambiguous()
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
    public void Catalog_resolves_when_namespace_differs_from_module_path()
    {
        var catalog = DeclarationCatalog.Create(LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                ["D5/S0/A/B/C.lean"] = new([], [Declaration("D5.S0.A.B.decl", "theorem")]),
            }));

        var resolved = catalog.Resolve(DeclarationHandle.Create("D5/S0/A/B/C.decl"));

        Assert.Equal("D5.S0.A.B.decl", resolved.Declaration.Name);
    }

    [Fact]
    public void Catalog_does_not_match_the_same_short_name_across_modules()
    {
        var catalog = DeclarationCatalog.Create(LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                ["D5/S0/Test/X.lean"] = new([], []),
                ["D5/S0/Test/Y.lean"] = new([], [Declaration("D5.S0.Test.Y.decl", "theorem")]),
            }));

        Assert.Throws<InvalidOperationException>(
            () => catalog.Resolve(DeclarationHandle.Create("D5/S0/Test/X.decl")));
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
            AuthoredStatement(),
            AssessedProvenance.FromRepo(),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Narrative"))));

        var error = Assert.Throws<InvalidOperationException>(() => catalog.ResolveKind(describe));

        Assert.Contains("cannot be projected to a Describe kind", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("unsupported kind", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Public_markdown_writer_rejects_unresolved_inductive_without_a_role()
    {
        var describe = Describe.Lean(
            DescribeId.Create("claim"),
            DeclarationHandle.Create(Gid),
            DefinitionDsl.H("Claim"),
            AuthoredStatement(),
            AssessedProvenance.FromRepo(),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Narrative"))));
        var document = ScribeNode.Create(
            "Digest",
            DefinitionDsl.H("Title"),
            DefinitionDsl.Blocks(describe),
            sourcePath: "/repo/Blueprint/D5/S0/Computability/SemanticLayerShift.scribe.cs");
        var catalog = DeclarationCatalog.Create(Report(Declaration(CanonicalName, "inductive")));

        Assert.Throws<InvalidOperationException>(() => CanonicalMarkdownWriter.Write(document, catalog));
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
    public void ScribeNode_preserves_edges_and_external_anchors()
    {
        const string path = "/repo/Blueprint/D5/S0/Computability/SemanticLayerShift.scribe.cs";
        var edge = DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Carrier/Ring"));
        var anchor = Anchor.ParseCanonical(
            "mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf");

        var document = ScribeNode.Create(
            "Digest",
            DefinitionDsl.H("Title"),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Content"))),
            edges: [edge],
            anchors: [anchor],
            sourcePath: path);

        var dependency = Assert.IsType<DocumentEdge.Dependency>(Assert.Single(document.Edges));
        Assert.Equal("D5/S0/Carrier/Ring", dependency.Target.Value);
        Assert.Equal(
            "mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf",
            Assert.Single(document.Header.Anchors).CanonicalString);
        Assert.Equal("D5/S0/Computability/SemanticLayerShift", document.Header.Gid.Value);
    }

    [Fact]
    public void Lean_describe_signature_has_no_repeated_formal_fields()
    {
        var method = typeof(Describe).GetMethod(nameof(Describe.Lean), BindingFlags.Public | BindingFlags.Static);
        Assert.NotNull(method);
        Assert.Equal(
            [typeof(DescribeId), typeof(DeclarationHandle), typeof(Heading),
             typeof(StatementSource), typeof(AssessedProvenance), typeof(BlockSequence), typeof(DescribeRole?)],
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
            DefinitionDsl.H("Claim"), AuthoredStatement(), AssessedProvenance.NovelAfterSearch(receipt),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Narrative"))));

        var assessed = Assert.IsType<AssessedProvenance.SuspectedNovel>(describe.AssessedProvenance);
        Assert.Equal(receipt, assessed.SearchReceipt);
    }

    [Fact]
    public void Unresolved_kind_error_identifies_the_describe_and_declaration()
    {
        var describe = Describe.Lean(
            DescribeId.Create("claim"), DeclarationHandle.Create(Gid),
            DefinitionDsl.H("Claim"), AuthoredStatement(), AssessedProvenance.FromRepo(),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Narrative"))));

        var exception = Assert.Throws<InvalidOperationException>(() => describe.Kind);

        Assert.Contains("Describe 'claim'", exception.Message, StringComparison.Ordinal);
        Assert.Contains(Gid, exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void LeanAxiomReportTypeBoundaryHasOnlyExplicitPublicParsingEntrypoints()
    {
        var scribeAssembly = typeof(DeclarationCatalog).Assembly;
        var publicMembers = scribeAssembly.ExportedTypes
            .SelectMany(static type => type
                .GetMethods(BindingFlags.Public | BindingFlags.Static | BindingFlags.Instance)
                .Cast<MethodBase>()
                .Concat(type.GetConstructors(BindingFlags.Public | BindingFlags.Instance)))
            .Distinct()
            .Where(static member => MemberTouchesLeanReport(member))
            .ToArray();

        var parsingBoundaries = new MethodBase[]
        {
            // Converts the raw compiled-artifact report into the governed declaration catalog.
            typeof(DeclarationCatalog).GetMethod(nameof(DeclarationCatalog.Create))!,
            // Legacy reference resolution turns one report entry into a verified declaration.
            typeof(LeanReferenceResolver).GetMethod(nameof(LeanReferenceResolver.Resolve))!,
        };

        Assert.Equal(
            parsingBoundaries.OrderBy(MemberSignature),
            publicMembers.OrderBy(MemberSignature));
    }

    private static bool MemberTouchesLeanReport(MethodBase member) =>
        member.GetParameters().Any(static parameter => TypeTouchesLeanReport(parameter.ParameterType))
        || member is MethodInfo method && TypeTouchesLeanReport(method.ReturnType);

    private static bool TypeTouchesLeanReport(Type type) =>
        type == typeof(LeanAxiomReport)
        || type.HasElementType && TypeTouchesLeanReport(type.GetElementType()!)
        || type.IsGenericType && type.GetGenericArguments().Any(TypeTouchesLeanReport);

    private static string MemberSignature(MethodBase member) =>
        $"{member.DeclaringType!.FullName}.{member.Name}({string.Join(",", member.GetParameters().Select(static parameter => parameter.ParameterType.FullName))})";

    private const string Gid = "D5/S0/Computability/SemanticLayerShift.claim";
    private const string CanonicalName = "D5.S0.Computability.SemanticLayerShift.claim";
    private const string SemanticLayerShiftLeanPath = "D5/S0/Computability/SemanticLayerShift.lean";

    private static StatementSource AuthoredStatement() =>
        StatementSource.FromAuthor(FormulaDsl.Disp(FormulaDsl.D(1)));

    private static LeanAxiomReport Report(params LeanDeclaration[] declarations) =>
        LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [SemanticLayerShiftLeanPath] = new(
                ImmutableArray<string>.Empty,
                declarations.ToImmutableArray()),
        });

}
