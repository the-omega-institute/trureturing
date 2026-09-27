using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ZeroQuantumPairsRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ZeroQuantumPairsRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/mathar2012a108958");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The number a(n) of unordered pairs of distinct binary words of length n with the same number of 1's (the zero-quantum transitions of n spins 1/2) satisfies n(n - 2)a(n) + 2(-3n^2 + 7n - 3)a(n - 1) + 4(n - 1)(2n - 3)a(n - 2) = 0 for every n at least 2, as conjectured by R. J. Mathar for OEIS A108958.",
        H("Mathar's recurrence for A108958"),
        Blocks(
            Node("a", "Pairs of words with equal weight", AFormula(),
                "The number of unordered pairs of distinct binary words of length n with the same number of 1's: for each k, the pairs among the choose(n, k) words with k ones.",
                "a", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Mathar's conjecture", ClaimFormula(),
                "For every n at least 2 the three-term recurrence with polynomial coefficients holds.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the recurrence", Disp(F.Id("claim")),
                "Since C(c, 2) = c(c - 1)/2, twice a(n) is the sum of the squares of the binomial coefficients C(n, k) minus their sum, that is C(2n, n) - 2^n. The central binomial coefficients satisfy (k + 1)C(2k + 2, k + 1) = 2(2k + 1)C(2k, k); applying this twice turns the recurrence for C(2n, n) into 2[(n - 2)(2n - 1) - (3n^2 - 7n + 3) + (n - 1)^2] C(2n - 2, n - 1) = 0, and 2^n satisfies it because 4n(n - 2) - 4(3n^2 - 7n + 3) + 4(n - 1)(2n - 3) = 0. The recurrence is linear, so a(n) satisfies it.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathar-2012-a108958-recurrence"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("zqpairs-" + id), DeclarationHandle.Create(Prefix + declaration),
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
    private static Formula Choose(Formula n, Formula k) => Call("choose", n, k);

    private static Formula AFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        Formula range = Call("range", Add(n, D(1)));
        return Disp(Equal(Call("a", n),
            Seq(Sum, Underscore, Grp(k, Sp, InMacro, Sp, range), Sp, Choose(Choose(n, k), D(2)))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n");
        Formula t1 = Times(Times(n, Parenthesized(Subtract(n, D(2)))), Call("a", n));
        Formula c2 = Parenthesized(Subtract(Add(Times(new Formula.Negate(D(3)), new Formula.Power(n, D(2))),
            Times(D(7), n)), D(3)));
        Formula t2 = Times(Times(D(2), c2), Call("a", Subtract(n, D(1))));
        Formula t3 = Times(Times(Times(D(4), Parenthesized(Subtract(n, D(1)))),
            Parenthesized(Subtract(Times(D(2), n), D(3)))), Call("a", Subtract(n, D(2))));
        return Disp(Iff(F.Id("claim"), All("n", Naturals(), Implies(AtMost(D(2), n),
            Equal(Add(Add(t1, t2), t3), D(0))))));
    }
}
