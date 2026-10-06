using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental;

internal sealed class PanSkanderaWangAllSplitsReverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsReverse.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pan2026permanental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The defining submatrix expression reverses both rows and columns.",
        H("PanSkanderaWangAllSplitsReverse"),
        Blocks(
            Node("reversematrix", "reverseMatrix", "reverseMatrix",
                reverseMatrixFormula(),
                "The defining submatrix expression reverses both rows and columns. FinRev(n) is the function Fin.rev on Fin n.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula reverseMatrixFormula() => Disp(
        All("n", Naturals(), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), Equal(Call("reverseMatrix", F.Id("A")), Call("submatrix", F.Id("A"), Call("FinRev", F.Id("n")), Call("FinRev", F.Id("n")))))));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Naturals() => Seq(Mathbb, Sp, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Sp, Grp(F.Id("R")));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
