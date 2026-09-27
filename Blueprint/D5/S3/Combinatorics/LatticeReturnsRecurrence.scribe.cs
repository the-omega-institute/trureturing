using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class LatticeReturnsRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LatticeReturnsRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/mathar2012a068551");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sequence a(n) = 4^n - binomial(2n, n), the total number of returns to the axis in all lattice paths with steps (1,1) and (1,-1) from the origin to (2n, 0), satisfies n a(n) + 2(3 - 4n) a(n - 1) + 8(2n - 3) a(n - 2) = 0 for every n at least 2, as conjectured by R. J. Mathar for OEIS A068551.",
        H("Mathar's recurrence for A068551"),
        Blocks(
            Node("a", "The sequence A068551", AFormula(),
                "a(n) = 4^n - binomial(2n, n), the name of the entry; it counts the returns to the x axis in all lattice paths with steps (1,1) and (1,-1) from the origin to (2n, 0).",
                "a", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Mathar's conjecture", ClaimFormula(),
                "For every n at least 2 the three-term recurrence with linear coefficients holds.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the recurrence", Disp(F.Id("claim")),
                "Write u(n) = choose(2n, n) and v(n) = 4^n. The central binomial coefficients satisfy n u(n) = 2(2n - 1) u(n - 1), and v(n) = 4 v(n - 1). Substituting a = v - u, the left side of the recurrence equals -R(0) + 4 R(1) + n S(0) - 2(2n - 3) S(1), where R(0) = n u(n) - 2(2n - 1) u(n - 1), R(1) = (n - 1) u(n - 1) - 2(2n - 3) u(n - 2), S(0) = v(n) - 4 v(n - 1) and S(1) = v(n - 1) - 4 v(n - 2) all vanish.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathar-2012-a068551-recurrence"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("latret-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula AFormula()
    {
        Formula n = F.Id("n");
        return Disp(Equal(Call("a", n),
            Subtract(new Formula.Power(D(4), n), Call("choose", Times(D(2), n), n))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n");
        Formula t1 = Times(n, Call("a", n));
        Formula t2 = Times(Times(D(2), Parenthesized(Subtract(D(3), Times(D(4), n)))), Call("a", Subtract(n, D(1))));
        Formula t3 = Times(Times(D(8), Parenthesized(Subtract(Times(D(2), n), D(3)))), Call("a", Subtract(n, D(2))));
        return Disp(Iff(F.Id("claim"), All("n", Naturals(), Implies(AtMost(D(2), n),
            Equal(Add(Add(t1, t2), t3), D(0))))));
    }
}
