using System.Reflection;

namespace StrataLint.Scribe.Tests;

public sealed class DescribeAstTests
{
    [Fact]
    public void DescribeHasNoPublicLegacyKindFactories()
    {
        Assert.Empty(typeof(DocumentBlock.Describe).GetConstructors(BindingFlags.Instance | BindingFlags.Public));

        var factories = typeof(DocumentBlock.Describe)
            .GetMethods(BindingFlags.Static | BindingFlags.Public)
            .Where(static method => method.ReturnType == typeof(DocumentBlock.Describe))
            .OrderBy(static method => method.Name, StringComparer.Ordinal)
            .ToArray();

        Assert.Empty(factories);
    }

    [Fact]
    public void LeanFacadeFailsClosedForNullStatementSourceAtRuntime()
    {
        var factory = typeof(Describe).GetMethod(
            nameof(Describe.Lean),
            BindingFlags.Static | BindingFlags.Public);
        Assert.NotNull(factory);

        var exception = Assert.Throws<TargetInvocationException>(() => factory.Invoke(
            null,
            [
                DescribeId.Create("required-claim"),
                DeclarationHandle.Create("D5/S1/Phase/Basic.required_claim"),
                Heading.Create("Required claim"),
                null,
                AssessedProvenance.FromRepo(),
                DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Content."))),
                DescribeRole.Theorem,
            ]));

        Assert.IsType<ArgumentNullException>(exception.InnerException);
    }

    [Fact]
    public void DescribeNodeCarriesKindStatementProvenanceAndContent()
    {
        var provenance = AssessedProvenance.FromRepo();
        var content = BlockSequence.Create(
        [
            new DocumentBlock.Paragraph(InlineSequence.Create(
            [
                new Inline.Text(TextRun.Create("Repository consequence.")),
            ])),
        ]);

        var describe = Describe.Lean(
            DescribeId.Create("golden-generator"),
            DeclarationHandle.Create("D5/S1/Phase/Basic.golden_generator"),
            Heading.Create("Golden generator"),
            StatementSource.FromAuthor(new Formula.Layout(
                FormulaLayoutMode.Inline,
                new Formula.Relation(
                    new Formula.Power(new Formula.Phi(), new Formula.Number(2)),
                    FormulaRelationOperator.Equal,
                    new Formula.Binary(
                        new Formula.Phi(),
                        FormulaBinaryOperator.Add,
                        new Formula.Number(1))))),
            provenance,
            content,
            DescribeRole.Definition);

        Assert.Equal("golden-generator", describe.Id.Value);
        Assert.Equal(DescribeKind.Definition, describe.Kind);
        Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);
        Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.ProvenanceKind);
        Assert.IsType<AssessedProvenance.RepoDerived>(describe.AssessedProvenance);
        Assert.Same(content, describe.Content);
        Assert.Equal("$\\varphi^{2} = \\varphi + 1$", describe.StatementFormula is null ? null : LatexWriter.WriteStatement(describe.StatementFormula));
    }

    [Fact]
    public void RepoDerivedProvenanceCanCarryTypedAcknowledgements()
    {
        var factory = Assert.Single(
            typeof(AssessedProvenance).GetMethods(BindingFlags.Static | BindingFlags.Public),
            static method => method.Name == nameof(AssessedProvenance.FromRepo)
                && method.GetParameters() is [{ ParameterType: var parameterType }]
                && parameterType == typeof(LibraryNoteRef[]));
        var landau = LibraryNoteRef.Create("D5/L/Quantum/landau1987violation");

        var provenance = Assert.IsAssignableFrom<AssessedProvenance>(
            factory.Invoke(null, [new[] { landau }]));
        var acknowledgementProperty = Assert.IsAssignableFrom<System.Collections.IEnumerable>(
            provenance.GetType().GetProperty("Acknowledgements")?.GetValue(provenance));

        Assert.Equal(
            [landau],
            acknowledgementProperty.Cast<LibraryNoteRef>());
    }

    [Fact]
    public void DescribeStatementIsAClosedFormulaOrLeanReferenceChoice()
    {
        var formula = DescribeStatement.FromFormula(new Formula.Phi());
        var lean = DescribeStatement.FromLean(LeanDeclarationRef.Create(
            "D5/S1/Scale/Embedding.embedding_injective"));

        Assert.IsType<DescribeStatement.FormulaAst>(formula);
        Assert.IsType<DescribeStatement.LeanDeclaration>(lean);
        Assert.Throws<ArgumentNullException>(() => DescribeStatement.FromFormula(null!));
        Assert.Throws<ArgumentNullException>(() => DescribeStatement.FromLean(null!));
    }

    [Fact]
    public void DescribeStatementVariantsCannotBypassFactoriesOrStoreNull()
    {
        var variants = new[]
        {
            (Type: typeof(DescribeStatement.FormulaAst), ValueType: typeof(Formula)),
            (Type: typeof(DescribeStatement.LeanDeclaration), ValueType: typeof(LeanDeclarationRef)),
        };

        foreach (var variant in variants)
        {
            var constructor = Assert.Single(
                variant.Type.GetConstructors(
                    BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic),
                candidate => candidate.GetParameters() is [{ ParameterType: var parameterType }]
                    && parameterType == variant.ValueType);
            Assert.True(constructor.IsPrivate);
            var exception = Assert.Throws<TargetInvocationException>(() =>
                constructor.Invoke([null]));
            Assert.IsType<ArgumentNullException>(exception.InnerException);
        }
    }

    [Fact]
    public void DescribeVocabularyIsClosedAtTheSixRuledKinds()
    {
        Assert.Equal(
            [
                DescribeKind.Definition,
                DescribeKind.Theorem,
                DescribeKind.Proposition,
                DescribeKind.Lemma,
                DescribeKind.Example,
                DescribeKind.Remark,
            ],
            Enum.GetValues<DescribeKind>());
        Assert.Equal(
            [
                DescribeProvenanceKind.LiteratureAttested,
                DescribeProvenanceKind.RepoDerived,
                DescribeProvenanceKind.SuspectedNovel,
            ],
            Enum.GetValues<DescribeProvenanceKind>());
    }

    [Theory]
    [InlineData("raw $x$ delimiter")]
    [InlineData("raw $$x$$ delimiter")]
    [InlineData("raw \\(x\\) delimiter")]
    [InlineData("raw \\[x\\] delimiter")]
    public void TextRunRejectsRawLatexDelimiters(string value)
    {
        Assert.Throws<ArgumentException>(() => TextRun.Create(value));
    }

    [Fact]
    public void DescribeRejectsMissingRequiredFields()
    {
        var provenance = AssessedProvenance.FromRepo();
        var id = DescribeId.Create("required-claim");
        var handle = DeclarationHandle.Create("D5/S1/Phase/Basic.required_claim");
        var statement = StatementSource.WithoutFormula();
        var content = BlockSequence.Create(
        [
            new DocumentBlock.Paragraph(InlineSequence.Create(
            [
                new Inline.Text(TextRun.Create("Required content.")),
            ])),
        ]);

        Assert.Throws<ArgumentNullException>(() => Describe.Lean(
            null!,
            handle,
            Heading.Create("Missing ID"),
            statement,
            provenance,
            content,
            DescribeRole.Definition));
        Assert.Throws<ArgumentNullException>(() => Describe.Lean(
            id,
            handle,
            null!,
            statement,
            provenance,
            content,
            DescribeRole.Definition));
        Assert.Throws<ArgumentNullException>(() => Describe.Lean(
            id,
            handle,
            Heading.Create("Missing statement"),
            null!,
            provenance,
            content,
            DescribeRole.Definition));
        Assert.Throws<ArgumentNullException>(() => Describe.Lean(
            id,
            handle,
            Heading.Create("Missing provenance"),
            statement,
            null!,
            content,
            DescribeRole.Definition));
    }

    [Fact]
    public void DocumentRejectsDuplicateDescribeIdsAcrossNestedBlocks()
    {
        DocumentBlock.Describe CreateDescribe(string title) => Describe.Remark(
            DescribeId.Create("same-claim"),
            Heading.Create(title),
            new Formula.Phi(),
            AssessedProvenance.FromRepo(),
            BlockSequence.Create(
            [
                DefinitionDsl.Paragraph(DefinitionDsl.Text("Typed content.")),
            ]));

        Assert.Throws<ArgumentException>(() => ScribeDocument.Create(
            DefinitionDsl.Header("D5/S1/Phase/Basic", "Duplicate ID fixture."),
            Heading.Create("Duplicate IDs"),
            BlockSequence.Create(
            [
                CreateDescribe("First"),
                new DocumentBlock.Section(
                    Heading.Create("Nested"),
                    BlockSequence.Create([CreateDescribe("Second")])),
            ])));
    }
}
