using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental;

internal sealed class PanSkanderaWangAllSplitsBalancedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBalanced.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pan2026permanental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every order at least four, the alternating principal permanent product is at most the product for the balanced initial split.",
        H("PanSkanderaWangAllSplitsBalanced"),
        Blocks(
            Node("balanced", "balanced", "balanced",
                balancedFormula(),
                "For every order at least four, the alternating principal permanent product is at most the product for the balanced initial split. natDiv is natural-number division, so natDiv(n,2) is the floor of n/2. The recursive bijection pairs the terms, and the rank-to-chain construction proves each paired monomial inequality.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula balancedFormula() => Disp(
        All("n", Naturals(), Implies(LessEqual(D(4), F.Id("n")), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), Implies(Call("TNN", F.Id("A")), LessEqual(Multiply(Call("principalPermanent", F.Id("A"), Call("evenIndices", F.Id("n"))), Call("principalPermanent", F.Id("A"), Seq(Call("univ", Call("Fin", F.Id("n"))), Sp, Setminus, Sp, Call("evenIndices", F.Id("n"))))), Multiply(Call("principalPermanent", F.Id("A"), Call("prefixIndices", F.Id("n"), Call("natDiv", F.Id("n"), D(2)))), Call("principalPermanent", F.Id("A"), Seq(Call("univ", Call("Fin", F.Id("n"))), Sp, Setminus, Sp, Call("prefixIndices", F.Id("n"), Call("natDiv", F.Id("n"), D(2))))))))))));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Naturals() => Seq(Mathbb, Sp, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Sp, Grp(F.Id("R")));

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
