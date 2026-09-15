using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class PerryLeastFactorialDivisibleByPrefixLcmDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/PerryLeastFactorialDivisibleByPrefixLcm.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/perry2004a094802");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prefix lcm divides the factorial of its largest prime, which is the least factorial index.",
        H("Perry's Least Factorial Index for the Prefix Lcm"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a094802-maximal-prime-factorial"),
                DeclarationHandle.Create(Prefix + "prefix_lcm_dvd_factorial_of_maximal_prime"),
                H("The maximal-prime factorial contains the prefix lcm"),
                StatementSource.FromAuthor(EndpointFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For n at least five and any prime p at least as large as every prime "
                        + "not exceeding n, the lcm of 1 through n divides p!. This is "
                        + "stronger than the membership half of the least-index result: "
                        + "it does not require p at most n. It can also be used in later "
                        + "prime-gap and Chebyshev estimates. The pinned lcmUpto factorial "
                        + "endpoint only yields divisibility by n!, whereas the prime-gap "
                        + "bound and the nonprime square and nonsquare cases lower it to p!."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a094802-least-factorial-index"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The maximal prime is the least factorial index"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Let S(n) be the set of natural k for which the lcm of 1 through n "
                        + "divides k!. For n at least five, a prime p at most n that "
                        + "bounds every prime not exceeding n is the least element of S(n). "
                        + "The maximal-prime factorial lemma supplies membership. Any k "
                        + "in S(n) has p dividing k!, so prime factorial divisibility "
                        + "implies p at most k. The upper bound uses Bertrand's prime gap "
                        + "and a prime-power factorial estimate, including the square case."))),
                DescribeRole.Theorem))));

    private static Formula EndpointFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p");
        return Disp(ForAll([Bound("n"), Bound("p")],
            Implies(And(Le(D(5), n), Prime(p), MaximalPrime(n, p)),
                Dvd(LcmUpto(n), Factorial(p)))));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p");
        return Disp(ForAll([Bound("n"), Bound("p")],
            Implies(And(Le(D(5), n), Prime(p), Le(p, n), MaximalPrime(n, p)),
                Call("IsLeast", Call("S", n), p))));
    }

    private static Formula MaximalPrime(Formula n, Formula p)
    {
        Formula q = F.Id("q");
        return ForAll([Bound("q")],
            Implies(And(Prime(q), Le(q, n)), Le(q, p)));
    }

    private static Formula Factorial(Formula value) => Seq(value, Bang);

    private static Formula LcmUpto(Formula n) => Call("lcmUpto", n);

    private static Formula Prime(Formula value) => Call("Prime", value);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name) =>
        new(FormulaIdentifier.Create(name), new Formula.NamedConstant(FormulaIdentifier.Create("Nat")));

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula And(Formula first, params Formula[] rest)
    {
        Formula result = rest[^1];
        for (int i = rest.Length - 1; i >= 0; i--)
        {
            Formula left = i == 0 ? first : rest[i - 1];
            result = new Formula.Logic(Parenthesized(left),
                FormulaLogicOperator.And, Parenthesized(result));
        }
        return result;
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Dvd(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
}
