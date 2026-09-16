using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Mersenne;

internal sealed class KrizekSigmaPrimeFermatMersenneDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Mersenne/KrizekSigmaPrimeFermatMersenne.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/krizek2014a249759");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime divisor sums force a prime-power input and the Fermat-Mersenne forms "
            + "conjectured for OEIS A249759.",
        H("Krizek's A249759 Fermat-Mersenne Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a249759-sigma-prime-input"),
                DeclarationHandle.Create(Prefix + "sigma_one_prime_imp_prime_pow"),
                H("A prime divisor sum has prime-power input"),
                StatementSource.FromAuthor(SigmaPrimeInputFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "All variables are natural numbers. The named operator sigma with "
                        + "subscript one is the sum-of-divisors function, so sigma sub one "
                        + "of m sums the first powers of all positive divisors of m. If this "
                        + "value is prime, the multiplicative factorization over all prime "
                        + "divisors of m forces that set to have one member. Thus m is a "
                        + "positive power of a prime."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a249759-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A249759 primes have Fermat and Mersenne form"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Here sigma sub one has the same divisor-sum convention. The hypotheses "
                        + "exclude p equal to two because sigma sub one of one is one; hence "
                        + "natural subtraction in p minus one is not truncated. The preceding "
                        + "prime-power theorem makes p minus one a power of two. Primality of "
                        + "p makes its exponent a power of two, while primality of the geometric "
                        + "divisor sum makes the Mersenne exponent prime. This proves items 2 "
                        + "and 3 of the cited conjecture only."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a249759-krizek-sigma-prime-fermat-mersenne"),
                    ResolutionKind.Proved)))));

    private static Formula SigmaPrimeInputFormula()
    {
        Formula m = F.Id("m");
        Formula q = F.Id("q");
        Formula k = F.Id("k");
        Formula conclusion = ExistsMany(
            [Bound("q"), Bound("k")],
            And(
                Prime(q),
                AtLeastOne(k),
                Equal(m, Power(q, k))));
        return Universal("m", Implies(Prime(SigmaOne(m)), conclusion));
    }

    private static Formula ResultFormula()
    {
        Formula p = F.Id("p");
        Formula m = F.Id("m");
        Formula r = F.Id("r");
        Formula pMinusOne = Subtract(p, D(1));
        Formula fermat = ExistsMany(
            [Bound("m")],
            Equal(p, Add(Power(D(2), Power(D(2), m)), D(1))));
        Formula mersenne = ExistsMany(
            [Bound("r")],
            And(
                Prime(r),
                Equal(SigmaOne(pMinusOne), Subtract(Power(D(2), r), D(1)))));
        return Universal(
            "p",
            Implies(
                And(Prime(p), Prime(SigmaOne(pMinusOne))),
                And(fermat, mersenne)));
    }

    private static Formula Universal(string variable, Formula body) => Disp(
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            Naturals(),
            body));

    private static Formula ExistsMany(
        Formula.BoundVariable[] variables,
        Formula body) => new Formula.BindMany(
            FormulaQuantifier.Exists,
            [.. variables],
            body);

    private static Formula.BoundVariable Bound(string name) =>
        new(FormulaIdentifier.Create(name), Naturals());

    private static Formula Prime(Formula value) =>
        new Formula.FunctionCall(FormulaIdentifier.Create("Prime"), [value]);

    private static Formula SigmaOne(Formula value) => Seq(
        Operatorname,
        Grp(F.Id("sigma")),
        Underscore,
        D(1),
        Parenthesized(value));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left),
            FormulaLogicOperator.Implies,
            Parenthesized(right));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]),
                FormulaLogicOperator.And,
                result);
        return result;
    }

    private static Formula AtLeastOne(Formula value) =>
        new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, value);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
}
