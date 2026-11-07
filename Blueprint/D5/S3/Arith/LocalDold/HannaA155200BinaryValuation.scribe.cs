using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.LocalDold;

internal sealed class HannaA155200BinaryValuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/LocalDold/HannaA155200BinaryValuation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/hanna2009a155200");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every coefficient of Hanna's A155200 exponential has an odd integer quotient by the power of two given by its binary digit sum.",
        H("Hanna A155200: exact binary valuation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hanna-a155200-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The literal exponential and the odd quotient"),
                StatementSource.FromAuthor(Disp(Equal(V("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "%N G.f.: A(x) = exp( Sum_{n>=1} 2^(n^2) * x^n/n ), a power series in x with integer coefficients. "
                    + "%C Conjecture: highest exponent of 2 dividing a(n) = A000120(n) = number of 1's in binary expansion of n, so that a(n)/2^A000120(n) is odd for n >= 0. - _Paul D. Hanna_, Sep 01 2009 "
                    + "OEIS A155200 has no page number; these are its NAME and COMMENTS lines, revision #39. "
                    + "PowerSeries.exp and PowerSeries.subst describe the formal exponential over the rationals. "
                    + "PowerSeries.coeff extracts ordinary coefficients. The exponent has zero constant coefficient. "
                    + "Nat.digits 2 n lists the binary digits, whose List.sum is the number of ones; the empty list at zero sums to zero. "
                    + "Odd applies to the integer z, which is then cast to the rationals. All natural indices, including zero, occur."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hanna-a155200-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The exact valuation holds at every natural index"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The geometric series with coefficients 2^n has integer coefficients. "
                    + "HannaDiagonalGhostPowerIntegrality.result transfers this integrality to the exponential with weights 2^(n^2). "
                    + "Differentiating gives the coefficient recurrence. Strong induction constructs integers b(n) with "
                    + "n! a(n)=2^n b(n) and b(n) congruent to one modulo four: the first normalized term is b(n-1), "
                    + "and every other term has a factor divisible by four. "
                    + "Legendre's factorial digit-sum identity and coprime cancellation give the odd integer z. "
                    + "No convergence or truncation condition is used."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("a155200-binaryvaluation"),
                    ResolutionKind.Proved)))));

    private static Formula ClaimBody()
    {
        var n = V("n");
        var z = V("z");
        var k = V("k");
        var coefficient = Call("ite", Equal(k, Num(0)), Num(0),
            new Formula.Fraction(Pow(Cast(Num(2), Rat()), Pow(k, Num(2))), Cast(k, Rat())));
        var exponent = App(Qualified("PowerSeries", "mk"), Lambda("k", Nat(), coefficient));
        var series = App(Qualified("PowerSeries", "subst"), exponent,
            App(Qualified("PowerSeries", "exp"), Rat()));
        var digits = App(Qualified("Nat", "digits"), Num(2), n);
        var digitSum = App(Qualified("List", "sum"), digits);
        return All("n", Nat(), Ex("z", Ints(),
            new Formula.Logic(Call("Odd", z), FormulaLogicOperator.And,
                Equal(App(Qualified("PowerSeries", "coeff"), n, series),
                    Multiply(Pow(Cast(Num(2), Rat()), digitSum), Cast(z, Rat()))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Rat() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula All(string name, Formula type, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(name), type)], body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.BindMany(
        FormulaQuantifier.Exists, [new(FormulaIdentifier.Create(name), type)], body);
}
