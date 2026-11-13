using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class KlineFactorialLcmTotientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/KlineFactorialLcmTotient.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/kline2017a025527");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kline's A025527 quotient equals the totient quotient at every positive integer prime index.",
        H("Kline's Factorial and Prefix Lcm Totient Quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kline-a025527-quotient"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The independent factorial quotient"),
                StatementSource.FromAuthor(QuotientFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each natural m, a(m) is m! divided by the least common multiple "
                    + "L(m) of the integers 1 through m. The quotient is taken in the rationals, "
                    + "and is defined independently of Euler's totient."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kline-a025527-totient-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The totient quotient at every prime minus one"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every integer j at least one, p is the j-th prime and m=p-1. "
                    + "Here p is Nat.nth Nat.Prime (j.toNat-1), translating the one-based "
                    + "integer index to the zero-based enumeration of all primes. "
                    + "Then a(m)=phi(m!)/phi(L(m)), with both ratios in the rationals. "
                    + "The case j=1 gives p=2 and m=1, with phi(1)=1. "
                    + "The factorial and prefix lcm have exactly the same prime divisors. "
                    + "Euler's prime-factor product for the totient therefore supplies a common "
                    + "multiplicative factor; the positive denominators permit cancellation. "
                    + "This mechanism does not use primality of p, although the stated domain "
                    + "is precisely Kline's prime-minus-one sequence."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a025527-kline-prime-minus-one-totient-quotient"),
                    ResolutionKind.Proved)))));

    private static Formula QuotientFormula()
    {
        Formula m = F.Id("m");
        return Disp(All("m", "Nat", Eq(Call("a", m), Ratio(Factorial(m), Call("L", m)))));
    }

    private static Formula ResultFormula()
    {
        Formula j = F.Id("j");
        Formula m = Seq(Call("nth", F.Id("Prime"),
            Seq(Call("toNat", j), Minus, D(1))), Minus, D(1));
        return Disp(All("j", "Int", new Formula.Logic(
            new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, j),
            FormulaLogicOperator.Implies,
            Eq(Call("a", m), Ratio(Call("phi", Factorial(m)), Call("phi", Call("L", m)))))));
    }

    private static Formula Factorial(Formula value) => Seq(Open, value, Close, Bang);
    private static Formula Ratio(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula All(string name, string type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            new Formula.NamedConstant(FormulaIdentifier.Create(type)), body);
}
