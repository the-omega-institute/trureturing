using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Recurrence;

internal sealed class MandalMohanFibonacciPowerMeanDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Arith/Recurrence/MandalMohanFibonacciPowerMean";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/Recurrence/mandalmohan2026integralmeans");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integrality of the quotient in Mandal and Mohan's Conjecture 1.19.",
        H("Mandal and Mohan's Fibonacci Power Means"),
        Blocks(Describe.Lean(
            DescribeId.Create("fibonacci-power-mean-integrality"),
            DeclarationHandle.Create(Owner + ".result"),
            H("Conjecture 1.19 holds for all positive prefix lengths and exponents at least three"),
            StatementSource.FromAuthor(Disp(Claim())),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("The Fibonacci numbers are indexed with F(1) = F(2) = 1. "
                    + "The sum includes both endpoints and all division takes place in the "
                    + "rationals. At prefix lengths one and two the quotients are 1 and "
                    + "2 raised to the exponent minus one, respectively.")),
                Paragraph(Text("The condition n ≥ 1 keeps the prefix nonempty. The source "
                    + "quotient is undefined for the empty prefix because its denominator is "
                    + "zero. With Lean's totalized rational division, n = 0 and k = 3 give "
                    + "the natural value 0, which lies outside the stated classification of "
                    + "prefix lengths. The condition k ≥ 3 excludes the case n = 3 and k = 2, "
                    + "where the quotient is 9 / (1 + 1 + 1/4) = 4 and the prefix length "
                    + "again lies outside the classification.")),
                Paragraph(Text("For a prefix of length at least eleven, Bertrand's postulate "
                    + "gives a prime index r strictly above the ceiling of half the length. "
                    + "A prime p dividing F(r) has first zero index r. The Fibonacci rank "
                    + "bound and parity give p at least 2r − 1, hence larger than the prefix "
                    + "length. Only F(r) in the prefix is divisible by p. Clearing denominators "
                    + "makes the sum of the scaled reciprocal powers coprime to p, so an "
                    + "integral quotient would be divisible by p raised to the exponent. "
                    + "The quotient is positive and strictly below the prefix length raised "
                    + "to the same exponent.")),
                Paragraph(Text("Lengths five through ten use explicit unique maximal prime "
                    + "powers 5, 8, or 13. At length four the cleared denominator is greater "
                    + "than one and coprime to 24. At length three it would have to be a power "
                    + "of three. Reduction modulo eight and factorization of a difference of "
                    + "squares then force the exponent to be two."))),
            DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var i = F.Id("i");
        var q = F.Id("q");
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var rationals = Seq(Mathbb, Grp(F.Id("Q")));
        var fibPower = Seq(F.Id("F"), Underscore, Grp(i), Caret, Grp(k));
        var reciprocal = Seq(Frac, Grp(D(1)), Grp(fibPower));
        var sum = Seq(Sum, Underscore, Grp(Seq(i, F.Eq, D(1))), Caret, Grp(n), Sp, reciprocal);
        var quotient = Seq(Frac, Grp(Seq(n, Caret, Grp(k))), Grp(sum));
        var integral = Seq(Open, Exists, Sp, q, InMacro, naturals, Comma, Sp,
            quotient, F.Eq, Open, q, Colon, rationals, Close, Close);
        return Seq(Forall, Sp, n, Comma, k, InMacro, naturals, Comma, Sp,
            Open, D(1), Le, Sp, n, Sp, Land, Sp, D(3), Le, Sp, k, Close, Sp, F.Implies, Sp,
            Open, integral, Sp, F.Iff, Sp,
            Open, n, F.Eq, D(1), Sp, Lor, Sp, n, F.Eq, D(2), Close, Close);
    }
}
