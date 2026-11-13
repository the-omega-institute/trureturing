using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class OriginalGenerationBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original finite return word is transported through an explicit 01 boundary.",
        H("Original Generation Boundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sigma-morphism"),
                DeclarationHandle.Create(
                    "D5/S1/Words/OriginalGenerationBoundary.sigma"),
                H("The original frontier morphism"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "sigma maps 0 to 01 and 1 to 0 on the explicit Bool word alphabet."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tau-morphism"),
                DeclarationHandle.Create(
                    "D5/S1/Words/OriginalGenerationBoundary.tau"),
                H("The marker-to-marker morphism"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "tau maps 0 to B5 = 00101 and 1 to B3 = 001, with the source orientation retained."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-word-application"),
                DeclarationHandle.Create(
                    "D5/S1/Words/OriginalGenerationBoundary.apply"),
                H("Applying a finite word morphism"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A morphism is applied letter by letter and the finite images are concatenated."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tau-word"),
                DeclarationHandle.Create(
                    "D5/S1/Words/OriginalGenerationBoundary.tauWord"),
                H("The finite marker-to-marker segment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "tauWord is the marker-to-marker segment obtained from an acquired finite return-type word."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-prefix"),
                DeclarationHandle.Create(
                    "D5/S1/Words/OriginalGenerationBoundary.finitePrefix"),
                H("The retained finite prefix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite prefix keeps the U_K prefix, appends the marker segment, and closes with 00."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("boundary-conjugacy-and-prefix"),
                DeclarationHandle.Create(
                    "D5/S1/Words/OriginalGenerationBoundary.original_generation_boundary"),
                H("Original generation through the explicit word boundary"),
                StatementSource.FromAuthor(BoundaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite return-type word, the third iterate of sigma is conjugate to tau "
                        + "through the displayed 01 boundary. The same theorem records the finite prefix "
                        + "identity with the distinct closing 00 marker. The statement is about explicit "
                        + "frontier words and does not assert a bracketed-tree or edit-history equality."))),
                DescribeRole.Theorem)),
        []));

    private static Formula BoundaryFormula()
    {
        var uK = F.Id("uK");
        var w = F.Id("w");
        var boolList = Seq(Operatorname, Grp(F.Id("List")), Sp, Operatorname, Grp(F.Id("Bool")));
        var zeroOne = Seq(OpenBracket, F.Id("false"), Comma, Sp, F.Id("true"), CloseBracket);
        var zeroZero = Seq(OpenBracket, F.Id("false"), Comma, Sp, F.Id("false"), CloseBracket);
        var boundary = Equal(
            Append(Call("sigmaThree", w), zeroOne),
            Append(zeroOne, Call("tauWord", w)));
        var prefix = Equal(
            Call("finitePrefix", uK, w),
            Append(Append(uK, Call("tauWord", w)), zeroZero));
        return Disp(Bind(FormulaQuantifier.ForAll, "uK", boolList,
            Bind(FormulaQuantifier.ForAll, "w", boolList, And(boundary, prefix))));
    }

    private static Formula Append(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Plus, Plus, Sp, Parenthesized(right));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Bind(FormulaQuantifier quantifier, string variable,
        Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
