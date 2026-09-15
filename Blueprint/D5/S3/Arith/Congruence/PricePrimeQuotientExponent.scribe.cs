using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class PricePrimeQuotientExponentDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/PricePrimeQuotientExponent.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/price2013a228558");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prime quotient (x^k+y^k)/(x+y) for coprime positive bases forces the exponent k to be prime.",
        H("Price's Prime-Quotient Exponents"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("price2013-prime-quotient-exponent"),
                DeclarationHandle.Create(Prefix + "prime_quotient_exponent_is_prime"),
                H("A prime odd-power quotient has prime exponent"),
                StatementSource.FromAuthor(GeneralFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For natural numbers x, y, and k with 1<=y<x and coprime x and y, "
                        + "suppose x+y divides x^k+y^k and the resulting quotient is prime. "
                        + "Then k is prime. Divisibility first forces k to be odd, while k=1 "
                        + "would make the quotient one. If k were odd and composite, a proper "
                        + "divisor d would place x^d+y^d strictly between x+y and x^k+y^k. "
                        + "The two induced quotient factors are nonunits whose product is the "
                        + "asserted prime quotient, a contradiction. This public general-purpose "
                        + "lemma supports both Price specializations and later arguments of the "
                        + "same form. The odd-power factorization supplied by "
                        + "Odd.nat_add_dvd_pow_add_pow is classical Mathlib material."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("price2013-a228558-result"),
                DeclarationHandle.Create(Prefix + "result_a228558"),
                H("Price's A228558 exponent conjecture"),
                StatementSource.FromAuthor(A228558Formula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural exponent k, if 21 divides 17^k+4^k and the exact "
                        + "quotient (17^k+4^k)/21 is prime, then k is prime. The explicit "
                        + "divisibility hypothesis prevents natural-number division from "
                        + "silently truncating. The general theorem applies because 4 is "
                        + "positive, 4<17, and 17 and 4 are coprime."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a228558-price-seventeen-four-prime-exponent"),
                    ResolutionKind.Proved)),
            Describe.Lean(
                DescribeId.Create("price2013-a231329-result"),
                DeclarationHandle.Create(Prefix + "result_a231329"),
                H("Price's A231329 exponent conjecture"),
                StatementSource.FromAuthor(A231329Formula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural exponent k, if 23 divides 19^k+4^k and the exact "
                        + "quotient (19^k+4^k)/23 is prime, then k is prime. The explicit "
                        + "divisibility hypothesis prevents natural-number division from "
                        + "silently truncating. The general theorem applies because 4 is "
                        + "positive, 4<19, and 19 and 4 are coprime."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a231329-price-nineteen-four-prime-exponent"),
                    ResolutionKind.Proved)))));

    private static Formula GeneralFormula()
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var k = F.Id("k");
        var numerator = Add(Power(x, k), Power(y, k));
        var denominator = Add(x, y);
        var hypotheses = And(
            LessOrEqual(D(1), y),
            And(
                Less(y, x),
                And(
                    Call("Coprime", x, y),
                    And(
                        Divides(denominator, numerator),
                        Call("Prime", Divide(numerator, denominator))))));
        return Disp(Universal(["x", "y", "k"], Implies(
            Parenthesized(hypotheses),
            Parenthesized(Call("Prime", k)))));
    }

    private static Formula A228558Formula() => InstanceFormula(D(2, 1), D(1, 7), D(4));

    private static Formula A231329Formula() => InstanceFormula(D(2, 3), D(1, 9), D(4));

    private static Formula InstanceFormula(Formula denominator, Formula x, Formula y)
    {
        var k = F.Id("k");
        var numerator = Add(Power(x, k), Power(y, k));
        return Disp(Universal(["k"], Implies(
            Parenthesized(Divides(denominator, numerator)),
            Parenthesized(Implies(
                Parenthesized(Call("Prime", Divide(numerator, denominator))),
                Parenthesized(Call("Prime", k)))))));
    }

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Universal(string[] names, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. names.Select(name =>
                new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals()))],
            body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Divide(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Slash, Sp, Parenthesized(right));

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
