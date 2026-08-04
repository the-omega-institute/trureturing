using System.Reflection;

namespace StrataLint.Scribe.Tests;

public sealed class DescribeAstTests
{
    [Fact]
    public void DescribeHasOnlyTheSixPublicKindFactories()
    {
        Assert.Empty(typeof(DocumentBlock.Describe).GetConstructors(BindingFlags.Instance | BindingFlags.Public));

        var factories = typeof(DocumentBlock.Describe)
            .GetMethods(BindingFlags.Static | BindingFlags.Public)
            .Where(static method => method.ReturnType == typeof(DocumentBlock.Describe))
            .OrderBy(static method => method.Name, StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(
            ["Definition", "Example", "Lemma", "Proposition", "Remark", "Theorem"],
            factories.Select(static method => method.Name));
        Assert.Equal(
            [
                typeof(DescribeId), typeof(Heading), typeof(LeanDeclarationRef),
                typeof(DescribeProvenance), typeof(BlockSequence), typeof(Formula),
            ],
            Assert.Single(factories, static method => method.Name == "Definition")
                .GetParameters().Select(static parameter => parameter.ParameterType));
        Assert.Equal(
            [
                typeof(DescribeId), typeof(Heading), typeof(Formula),
                typeof(DescribeProvenance), typeof(BlockSequence),
            ],
            Assert.Single(factories, static method => method.Name == "Example")
                .GetParameters().Select(static parameter => parameter.ParameterType));
        Assert.Equal(
            [
                typeof(DescribeId), typeof(Heading), typeof(DescribeStatement),
                typeof(DescribeProvenance), typeof(BlockSequence),
            ],
            Assert.Single(factories, static method => method.Name == "Remark")
                .GetParameters().Select(static parameter => parameter.ParameterType));
        foreach (var name in new[] { "Theorem", "Proposition", "Lemma" })
        {
            Assert.Equal(
                [
                    typeof(DescribeId), typeof(Heading), typeof(LeanDeclarationRef),
                    typeof(Formula), typeof(DescribeProvenance), typeof(BlockSequence),
                ],
                Assert.Single(factories, method => method.Name == name)
                    .GetParameters().Select(static parameter => parameter.ParameterType));
        }
    }

    [Fact]
    public void TheoremFactoryFailsClosedForNullLatexAtRuntime()
    {
        var factory = typeof(DocumentBlock.Describe).GetMethod(
            "Theorem",
            BindingFlags.Static | BindingFlags.Public);
        Assert.NotNull(factory);

        var exception = Assert.Throws<TargetInvocationException>(() => factory.Invoke(
            null,
            [
                DescribeId.Create("required-claim"),
                Heading.Create("Required claim"),
                DefinitionDsl.LeanTheorem("D5/S1/Phase/Basic.required_claim"),
                null,
                DescribeProvenance.RepoDerived(),
                DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Content."))),
            ]));

        Assert.IsType<ArgumentNullException>(exception.InnerException);
    }

    [Fact]
    public void DescribeNodeCarriesKindStatementProvenanceAndContent()
    {
        var provenance = DescribeProvenance.RepoDerived();
        var content = BlockSequence.Create(
        [
            new DocumentBlock.Paragraph(InlineSequence.Create(
            [
                new Inline.Text(TextRun.Create("Repository consequence.")),
            ])),
        ]);

        var describe = DocumentBlock.Describe.Definition(
            DescribeId.Create("golden-generator"),
            Heading.Create("Golden generator"),
            DefinitionDsl.LeanTheorem("D5/S1/Phase/Basic.golden_generator"),
            provenance,
            content,
            new Formula.Layout(
                FormulaLayoutMode.Inline,
                new Formula.Relation(
                    new Formula.Power(new Formula.Phi(), new Formula.Number(2)),
                    FormulaRelationOperator.Equal,
                    new Formula.Binary(
                        new Formula.Phi(),
                        FormulaBinaryOperator.Add,
                        new Formula.Number(1)))));

        Assert.Equal("golden-generator", describe.Id.Value);
        Assert.Equal(DescribeKind.Definition, describe.Kind);
        Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);
        Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);
        Assert.Same(content, describe.Content);
        Assert.Equal("$\\varphi^{2} = \\varphi + 1$", describe.StatementFormula is null ? null : LatexWriter.WriteStatement(describe.StatementFormula));
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
                DescribeProvenanceKind.Unassessed,
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
        var provenance = DescribeProvenance.RepoDerived();
        var id = DescribeId.Create("required-claim");
        var content = BlockSequence.Create(
        [
            new DocumentBlock.Paragraph(InlineSequence.Create(
            [
                new Inline.Text(TextRun.Create("Required content.")),
            ])),
        ]);

        Assert.Throws<ArgumentNullException>(() => DocumentBlock.Describe.Definition(
            null!,
            Heading.Create("Missing ID"),
            DefinitionDsl.LeanTheorem("D5/S1/Phase/Basic.required_claim"),
            provenance,
            content));
        Assert.Throws<ArgumentNullException>(() => DocumentBlock.Describe.Definition(
            id,
            null!,
            DefinitionDsl.LeanTheorem("D5/S1/Phase/Basic.required_claim"),
            provenance,
            content));
        Assert.Throws<ArgumentNullException>(() => DocumentBlock.Describe.Definition(
            id,
            Heading.Create("Missing statement"),
            null!,
            provenance,
            content));
        Assert.Throws<ArgumentNullException>(() => DocumentBlock.Describe.Definition(
            id,
            Heading.Create("Missing provenance"),
            DefinitionDsl.LeanTheorem("D5/S1/Phase/Basic.required_claim"),
            null!,
            content));
    }

    [Fact]
    public void DocumentRejectsDuplicateDescribeIdsAcrossNestedBlocks()
    {
        DocumentBlock.Describe Describe(string title) => DocumentBlock.Describe.Remark(
            DescribeId.Create("same-claim"),
            Heading.Create(title),
            DescribeStatement.FromFormula(new Formula.Phi()),
            DescribeProvenance.RepoDerived(),
            BlockSequence.Create(
            [
                DefinitionDsl.Paragraph(DefinitionDsl.Text("Typed content.")),
            ]));

        Assert.Throws<ArgumentException>(() => ScribeDocument.Create(
            DefinitionDsl.Header("D5/S1/Phase/Basic", "Duplicate ID fixture."),
            Heading.Create("Duplicate IDs"),
            BlockSequence.Create(
            [
                Describe("First"),
                new DocumentBlock.Section(
                    Heading.Create("Nested"),
                    BlockSequence.Create([Describe("Second")])),
            ])));
    }
}
