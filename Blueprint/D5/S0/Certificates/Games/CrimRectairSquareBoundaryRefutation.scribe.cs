using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Games;

internal sealed class CrimRectairSquareBoundaryRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/Games/CrimRectairSquareBoundaryRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/basic2026crim");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The printed square-rectair formula gives 2 at r=1 and k=0, but the value is 1.",
        H("The Boundary Counterexample to CRIM Conjecture 2"),
        Blocks(
            Node("crim-square-claim", "Conjecture 2 as printed", ClaimFormula(),
                "Conjecture 2 states verbatim: \"Let r and k be integers with 0 ≤ k < r. "
                    + "Then G(R^k_{r,r}) = 0 if r is even or k < r − 1; = 1 if "
                    + "r ∈ {3, 5}, r is odd, and k = r − 1; = 2 otherwise.\" "
                    + "The formal variables are natural numbers; k < r forces r to be "
                    + "positive. The statement uses the public grundy and rectair names "
                    + "from CrimGrundyRefutation. Here mod(r,2) is the natural-number "
                    + "remainder and r−1 is natural-number subtraction. In the second "
                    + "branch, failure of the first branch together with k < r implies "
                    + "that r is odd and k = r−1, so the nested conditional is equivalent "
                    + "to the printed three branches on the quantified domain.",
                "claim", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("crim-square-refutation", "The value at r=1 and k=0", ResultFormula(),
                "At r=1 and k=0, rectair(1,1,0) is the one-cell partition [1]. "
                    + "Its row and column deletions both reach the empty partition, so "
                    + "moves([1]) is [[],[]]. The empty partition has value 0, hence the "
                    + "least excluded option value is 1. The printed third branch gives 2. "
                    + "The same page's Conjecture 4 also gives the first stair value as 1. "
                    + "The theorem refutes only the literal printed Conjecture 2 and does "
                    + "not propose a corrected formula.",
                "result", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "crim-rectair-square-conjecture-two-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose, string declaration,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula ClaimFormula()
    {
        var r = F.Id("r");
        var k = F.Id("k");
        var firstCondition = Or(
            Equal(Call("mod", r, D(2)), D(0)),
            Less(k, Subtract(r, D(1))));
        var secondCondition = Or(Equal(r, D(3)), Equal(r, D(5)));
        var predicted = IfThenElse(firstCondition, D(0),
            IfThenElse(secondCondition, D(1), D(2)));
        var value = Call("grundy", Call("rectair", r, r, k));
        var body = Universal("r", Naturals(), Universal("k", Naturals(),
            Implies(Less(k, r), Equal(value, predicted))));
        return Disp(Iff(Parenthesized(F.Id("claim")), Parenthesized(body)));
    }

    private static Formula ResultFormula() => Disp(new Formula.Not(F.Id("claim")));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Universal(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula IfThenElse(
        Formula condition, Formula whenTrue, Formula whenFalse) => Parenthesized(Seq(
            Named("if"), Sp, Parenthesized(condition), Sp,
            Named("then"), Sp, whenTrue, Sp,
            Named("else"), Sp, whenFalse));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or,
            Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
}
