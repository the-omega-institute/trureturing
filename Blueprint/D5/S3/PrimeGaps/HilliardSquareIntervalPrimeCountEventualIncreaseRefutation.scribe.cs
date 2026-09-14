using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeGaps;

internal sealed class HilliardSquareIntervalPrimeCountEventualIncreaseRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeGaps/HilliardSquareIntervalPrimeCountEventualIncreaseRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/hilliard2003a089610");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd-prime counting rules out eventual strict increase for OEIS A089610.",
        H("The OEIS A089610 Eventual Strict-Increase Conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a089610-square-interval-prime-count"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The square-interval prime count"),
                StatementSource.FromAuthor(AFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The value a(n) counts the primes in the half-open interval "
                        + "(n^2, n^2+n]. Since (n+1/2)^2 = n^2+n+1/4, this interval "
                        + "contains the same integer primes as the printed OEIS interval."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a089610-eventual-strict-increase"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The eventual strict-increase conjecture"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The claim asks for a natural threshold N after which every "
                        + "successive value of a is strictly larger."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a089610-eventual-strict-increase-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Eventual strict increase is impossible"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "At every even index, the odd primes in the defining interval "
                        + "inject into k positions, giving a(2k) <= k. Strict increase "
                        + "through a window from M to 2M+2 would instead force the final "
                        + "value above this bound. The first conjecture a(n) > 1 after "
                        + "n = 17 and Oppermann's positivity conjecture are untouched."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a089610-square-interval-prime-count-eventual-increase-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula AFormula()
    {
        var n = F.Id("n");
        var lower = Multiply(n, n);
        var upper = Add(Multiply(n, n), n);
        var interval = Call("Ioc", lower, upper);
        var primes = Call("filter", Seq(F.Id("Nat"), Dot, F.Id("Prime")), interval);
        return Disp(ForAll("n", Naturals(),
            Equal(Call("a", n), Call("card", primes))));
    }

    private static Formula ClaimFormula()
    {
        var cutoff = F.Id("N");
        var n = F.Id("n");
        var increase = Less(Call("a", n), Call("a", Add(n, D(1))));
        var tail = ForAll("n", Naturals(),
            Implies(AtMost(cutoff, n), increase));
        return Disp(Iff(F.Id("claim"), Exists("N", Naturals(), tail)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff,
            Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
}
