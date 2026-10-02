using System.Globalization;
using System.Reflection;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeResourceAstCoverageTests
{
    public static IEnumerable<object[]> FormulaBranches()
    {
        var id = FormulaIdentifier.Create("x");
        var atom = new Formula.Symbol(id);
        var word = new Formula.LatexWord(id);
        yield return [new Formula.Aligned([atom])];
        yield return [new Formula.LatexSequence([word])];
        yield return [new Formula.LatexGroup([word])];
        yield return [new Formula.LatexMacro(FormulaLatexMacro.Alpha)];
        yield return [new Formula.LatexSymbol(FormulaLatexSymbol.Plus)];
        yield return [new Formula.LatexSpace()];
        yield return [new Formula.LatexNewline()];
        yield return [word];
        yield return [new Formula.LatexDigits([1, 2, 3])];
        yield return [new Formula.Layout(FormulaLayoutMode.Display, atom)];
        yield return [atom];
        yield return [new Formula.Number(3)];
        yield return [new Formula.Phi()];
        yield return [new Formula.Psi()];
        yield return [new Formula.Placeholder()];
        yield return [new Formula.Integers()];
        yield return [new Formula.NamedConstant(id)];
        yield return [new Formula.Negate(atom)];
        yield return [new Formula.Absolute(atom)];
        yield return [new Formula.Norm(atom)];
        yield return [new Formula.Binary(atom, FormulaBinaryOperator.Add, atom)];
        yield return [new Formula.Fraction(atom, atom)];
        yield return [new Formula.Subscript(atom, atom)];
        yield return [new Formula.Power(atom, atom)];
        yield return [new Formula.Floor(atom)];
        yield return [new Formula.Log(atom, atom)];
        yield return [new Formula.Modulo(atom, atom)];
        yield return [new Formula.Sequence(atom, atom, atom)];
        yield return [new Formula.SetLiteral([atom])];
        yield return [new Formula.SetBuilder(atom, atom, atom)];
        yield return [new Formula.FunctionCall(id, [atom])];
        yield return [new Formula.Apply(new Formula.FunctionCall(id, []), [atom])];
        yield return [new Formula.TypeArrow(atom, atom)];
        yield return [new Formula.Relation(atom, FormulaRelationOperator.Equal, atom)];
        yield return [new Formula.RelationChain(FormulaRelationOperator.Equal, [atom, atom])];
        yield return [new Formula.Logic(atom, FormulaLogicOperator.And, atom)];
        yield return [new Formula.Not(atom)];
        yield return [new Formula.Bind(FormulaQuantifier.ForAll, id, atom, atom)];
        yield return [new Formula.BindMany(FormulaQuantifier.Exists, [new Formula.BoundVariable(id, atom)], atom)];
    }

    [Fact]
    public void EveryFormulaBranchRoundTrips()
    {
        foreach (var item in FormulaBranches())
        {
            var definition = Definition((Formula)item[0]);
            var encoded = ScribeResourceCodec.Encode(definition);
            var decoded = ScribeResourceCodec.Decode(encoded);
            Assert.Equal(encoded, ScribeResourceCodec.Encode(decoded));
            Assert.True(ScribeResourceStructuralComparer.Equal(definition, decoded, out var difference), difference);
        }
    }

    [Fact]
    public void AllDocumentNodeFamiliesAndEdgesRoundTrip()
    {
        var declaration = DeclarationHandle.Create("D5/S1/Scale/Embedding.embedding_injective");
        var authored = DocumentBlock.Describe.Restore(
            DescribeId.Create("authored"),
            DefinitionDsl.H("Authored"),
            DescribeStatement.FromFormula(DefinitionDsl.Equal(DefinitionDsl.Id("x"), DefinitionDsl.Num(1))),
            AssessedProvenance.FromRepo(),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("narrative"))),
            null,
            null,
            new DescribeKindSource.Authored(DescribeKind.Remark));
        var declarationRemark = Describe.Remark(
            DescribeId.Create("remark"),
            declaration,
            DefinitionDsl.H("Remark"),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/sos1957threegap")),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("comment"))));
        var document = ScribeDocument.Create(
            DocumentHeader.Create(
                GidRef.Create("D5/S1/Scale/Resource"),
                Generality.Extremal,
                GidRef.Create("D5/B/S1/Scale/Resource"),
                new EvidenceMirror.Artifact(GidRef.Create("D5/E/S1/Scale/Resource.result--json")),
                [Anchor.ParseCanonical("mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf")],
                Digest.Create("digest")),
            DefinitionDsl.H("All nodes"),
            DefinitionDsl.Blocks(
                new DocumentBlock.Paragraph(InlineSequence.Create([
                    new Inline.Text(DefinitionDsl.T("text")),
                    new Inline.InlineFormula(DefinitionDsl.Num(2)),
                    new Inline.GidReference(GidRef.Create("D5/S1/Scale/Other"))])),
                new DocumentBlock.DisplayFormula(DefinitionDsl.Num(3)),
                new DocumentBlock.Section(DefinitionDsl.H("section"), DefinitionDsl.Blocks(authored)),
                declarationRemark),
            [
                DocumentEdge.TruthAnchor.Create(LeanDeclarationRef.Create(declaration.Value)),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Scale/Other")),
                DocumentEdge.NarrativeReference.ToDocument(GidRef.Create("D5/S1/Scale/Other")),
                DocumentEdge.NarrativeReference.ToDescribe(GidRef.Create("D5/S1/Scale/Other"), DescribeId.Create("remark")),
            ]);
        var definition = DocumentDefinition.Create(document, "Blueprint/D5/S1/Scale/Resource.scribe.cs");

        var encoded = ScribeResourceCodec.Encode(definition);
        var decoded = ScribeResourceCodec.Decode(encoded);
        Assert.Equal(encoded, ScribeResourceCodec.Encode(decoded));
        Assert.True(ScribeResourceStructuralComparer.Equal(definition, decoded, out var difference), difference);
    }

    [Fact]
    public void EncodingDoesNotDependOnCurrentCulture()
    {
        var definition = Definition(DefinitionDsl.Add(DefinitionDsl.Num(1), DefinitionDsl.Num(2)));
        var original = CultureInfo.CurrentCulture;
        try
        {
            CultureInfo.CurrentCulture = CultureInfo.GetCultureInfo("tr-TR");
            var first = ScribeResourceCodec.Encode(definition);
            CultureInfo.CurrentCulture = CultureInfo.GetCultureInfo("de-DE");
            Assert.Equal(first, ScribeResourceCodec.Encode(definition));
        }
        finally
        {
            CultureInfo.CurrentCulture = original;
        }
    }

    [Fact]
    public void EveryAstAbstractFamilyHasAnEncodedConcreteBranch()
    {
        var roundTripped = CoverageDefinitions()
            .Select(static definition => ScribeResourceCodec.Decode(ScribeResourceCodec.Encode(definition)))
            .ToArray();
        var roundTrippedTypes = new HashSet<Type>();
        foreach (var definition in roundTripped)
        {
            CollectAstTypes(definition, roundTrippedTypes, new HashSet<object>(ReferenceEqualityComparer.Instance));
        }

        var abstractFamilies = new[]
        {
            typeof(Inline),
            typeof(DocumentBlock),
            typeof(Formula),
            typeof(EvidenceMirror),
            typeof(DescribeKindSource),
            typeof(DescribeStatement),
            typeof(AssessedProvenance),
            typeof(StatementSource),
            typeof(NarrativeTarget),
            typeof(DocumentEdge),
        };

        foreach (var family in abstractFamilies)
        {
            var concreteTypes = family
                .GetNestedTypes(BindingFlags.Public | BindingFlags.NonPublic)
                .Where(type => !type.IsAbstract && family.IsAssignableFrom(type));
            foreach (var concreteType in concreteTypes)
            {
                Assert.Contains(concreteType, roundTrippedTypes);
            }
        }
    }

    [Fact]
    public void CoverageDoesNotCrossSatisfySameNamedConcreteTypes()
    {
        var familyA = typeof(SyntheticFamilyA);
        var familyB = typeof(SyntheticFamilyB);
        var sharedA = familyA.GetNestedType(nameof(SyntheticFamilyA.Shared), BindingFlags.Public | BindingFlags.NonPublic)!;
        var sharedB = familyB.GetNestedType(nameof(SyntheticFamilyB.Shared), BindingFlags.Public | BindingFlags.NonPublic)!;
        Assert.Equal(sharedA.Name, sharedB.Name);

        var actual = new HashSet<Type> { sharedA };
        Assert.Contains(sharedA, actual);
        Assert.DoesNotContain(sharedB, actual);
    }

    [Fact]
    public void CoverageDefinitionsPreserveAllInstanceProperties()
    {
        foreach (var definition in CoverageDefinitions())
        {
            var decoded = ScribeResourceCodec.Decode(ScribeResourceCodec.Encode(definition));
            Assert.True(ScribeResourceStructuralComparer.Equal(definition, decoded, out var difference), difference);
        }
    }

    [Fact]
    public void AuthoredAndNoFormulaProjectionGapFieldsSurviveRoundTrip()
    {
        var definition = CoverageDefinitions().First();
        var decoded = ScribeResourceCodec.Decode(ScribeResourceCodec.Encode(definition));
        var expected = definition.Document.Content.Items.OfType<DocumentBlock.Describe>()
            .Where(static item => item.StatementSource is StatementSource.Authored or StatementSource.NoFormula)
            .Where(static item => item.Id.Value != "claim").ToArray();
        var actual = decoded.Document.Content.Items.OfType<DocumentBlock.Describe>()
            .Where(static item => item.StatementSource is StatementSource.Authored or StatementSource.NoFormula)
            .Where(static item => item.Id.Value != "claim").ToArray();
        Assert.Equal(2, expected.Length);
        Assert.Equal(expected.Length, actual.Length);
        for (var index = 0; index < expected.Length; index++)
        {
            var expectedGap = Gap(expected[index].StatementSource!);
            var actualGap = Gap(actual[index].StatementSource!);
            Assert.NotNull(expectedGap);
            Assert.NotNull(actualGap);
            Assert.Equal(expectedGap.ReasonCode, actualGap.ReasonCode);
            Assert.Equal(expectedGap.OffendingSubject, actualGap.OffendingSubject);
            Assert.Equal(expectedGap.ProjectorEpoch, actualGap.ProjectorEpoch);
            Assert.Equal(expectedGap.DeclarationContentDigest, actualGap.DeclarationContentDigest);
        }

        static ProjectionGap? Gap(StatementSource source) => source switch
        {
            StatementSource.Authored authored => authored.ProjectionGap,
            StatementSource.NoFormula noFormula => noFormula.ProjectionGap,
            _ => null,
        };
    }

    private static void CollectAstTypes(object? value, ISet<Type> types, ISet<object> visited)
    {
        if (value is null || value is string || value.GetType().IsPrimitive || value.GetType().IsEnum)
        {
            return;
        }

        if (value is System.Collections.IEnumerable sequence)
        {
            foreach (var item in sequence)
            {
                CollectAstTypes(item, types, visited);
            }

            return;
        }

        var type = value.GetType();
        if (type.Namespace != typeof(Formula).Namespace || !visited.Add(value))
        {
            return;
        }

        types.Add(type);
        foreach (var property in type.GetProperties(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic))
        {
            if (property.GetIndexParameters().Length != 0 || property.GetMethod is null)
            {
                continue;
            }

            CollectAstTypes(property.GetValue(value), types, visited);
        }
    }

    private abstract class SyntheticFamilyA
    {
        public sealed class Shared : SyntheticFamilyA;
    }

    private abstract class SyntheticFamilyB
    {
        public sealed class Shared : SyntheticFamilyB;
    }

    private static DocumentDefinition Definition(Formula formula) => DocumentDefinition.Create(
        ScribeNode.Create(
            "digest",
            DefinitionDsl.H("Formula"),
            DefinitionDsl.Blocks(new DocumentBlock.DisplayFormula(formula)),
            sourcePath: "Blueprint/D5/S1/Scale/Resource.scribe.cs"),
        "Blueprint/D5/S1/Scale/Resource.scribe.cs");

    private static IEnumerable<DocumentDefinition> CoverageDefinitions()
    {
        var atom = new Formula.Symbol(FormulaIdentifier.Create("x"));
        var blocks = FormulaBranches()
            .Select(static item => (Formula)item[0])
            .Select(static formula => (DocumentBlock)new DocumentBlock.DisplayFormula(formula))
            .ToList();
        blocks.Add(new DocumentBlock.Paragraph(InlineSequence.Create([
            new Inline.Text(TextRun.Create("text")),
            new Inline.InlineFormula(atom),
            new Inline.GidReference(GidRef.Create("D5/S1/Scale/Other")),
        ])));
        blocks.Add(new DocumentBlock.Section(
            DefinitionDsl.H("section"),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("section content")))));
        blocks.Add(DocumentBlock.Describe.Restore(
            DescribeId.Create("authored"),
            DefinitionDsl.H("Authored"),
            DescribeStatement.FromFormula(atom),
            AssessedProvenance.FromRepo(),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("narrative"))),
            null,
            null,
            new DescribeKindSource.Authored(DescribeKind.Remark)));
        blocks.Add(DocumentBlock.Describe.Restore(
            DescribeId.Create("lean"),
            DefinitionDsl.H("Lean"),
            DescribeStatement.FromLean(LeanDeclarationRef.Create("D5/S1/Scale/Other.member")),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/sos1957threegap")),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("narrative"))),
            atom,
            StatementSource.FromLean(),
            new DescribeKindSource.ReportDerived(
                DeclarationHandle.Create("D5/S1/Scale/Other.member"),
                DescribeRole.Theorem)));
        blocks.Add(DocumentBlock.Describe.Restore(
            DescribeId.Create("authored-source"),
            DefinitionDsl.H("Authored source"),
            DescribeStatement.FromLean(LeanDeclarationRef.Create("D5/S1/Scale/Other.member")),
            AssessedProvenance.NovelAfterSearch(GidRef.Create("D5/S1/Scale/Search")),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("narrative"))),
            atom,
            new StatementSource.Authored(atom, new ProjectionGap(
                "missing", "D5/S1/Scale/Other.member", "statement-projector-v1", new string('a', 64))),
            new DescribeKindSource.ReportDerived(
                DeclarationHandle.Create("D5/S1/Scale/Other.member"),
                DescribeRole.Lemma)));
        blocks.Add(DocumentBlock.Describe.Restore(
            DescribeId.Create("no-formula"),
            DefinitionDsl.H("No formula"),
            DescribeStatement.FromLean(LeanDeclarationRef.Create("D5/S1/Scale/Other.member")),
            AssessedProvenance.FromRepo(),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("narrative"))),
            null,
            new StatementSource.NoFormula(new ProjectionGap(
                "constant", "Fixture.subject", "statement-projector-v1", new string('b', 64))),
            new DescribeKindSource.ReportDerived(
                DeclarationHandle.Create("D5/S1/Scale/Other.member"),
                DescribeRole.Proposition)));

        var claimSource = new StatementSource.Authored(atom, null);
        blocks.Add(DocumentBlock.Describe.ReportDerived(
            DescribeId.Create("claim"), DefinitionDsl.H("Claim"),
            DeclarationHandle.Create("D5/S1/Scale/Other.member"), claimSource,
            AssessedProvenance.FromRepo(),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("claim"))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("batch-problem"), ResolutionKind.Proved,
                [DeclarationHandle.Create("D5/S1/Scale/Other.additional")]),
            restoredStatement: (claimSource, atom)));

        DocumentEdge[] edges =
        [
            DocumentEdge.TruthAnchor.Create(LeanDeclarationRef.Create("D5/S1/Scale/Other.member")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Scale/Other")),
            DocumentEdge.NarrativeReference.ToDocument(GidRef.Create("D5/S1/Scale/Other")),
            DocumentEdge.NarrativeReference.ToDescribe(
                GidRef.Create("D5/S1/Scale/Other"),
                DescribeId.Create("authored")),
        ];
        yield return DocumentDefinition.Create(
            ScribeDocument.Create(
                DocumentHeader.Create(
                    GidRef.Create("D5/S1/Scale/AllAstBranches"),
                    Generality.Extremal,
                    GidRef.Create("D5/B/S1/Scale/AllAstBranches"),
                    new EvidenceMirror.Artifact(GidRef.Create("D5/E/S1/Scale/AllAstBranches.result--json")),
                    [],
                    Digest.Create("digest")),
                DefinitionDsl.H("All AST branches"),
                DefinitionDsl.Blocks(blocks.ToArray()),
                edges),
            "Blueprint/D5/S1/Scale/AllAstBranches.scribe.cs");
        yield return DocumentDefinition.Create(
            ScribeDocument.Create(
                DocumentHeader.Create(
                    GidRef.Create("D5/S1/Scale/WaiverBranch"),
                    Generality.Extremal,
                    GidRef.Create("D5/B/S1/Scale/WaiverBranch"),
                    new EvidenceMirror.Waiver(WaiverReason.Create("fixture")),
                    [],
                    Digest.Create("digest")),
                DefinitionDsl.H("Waiver branch"),
                DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("waiver")))),
            "Blueprint/D5/S1/Scale/WaiverBranch.scribe.cs");
    }
}
