using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class PrimeEulerLogTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The omitted-prime Euler logarithms have an explicit power-decay tail bound.",
        H("Prime Euler Logarithm Tail"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-euler-log-tail-le"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/SeriesInequalities/PrimeEulerLogTail.prime_euler_log_tail_le"),
            H("Explicit bound for omitted prime directions"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The sum ranges over natural primes strictly greater than the integer X. "
                    + "The parameter s is real and greater than one.")),
                Paragraph(Text(
                    "Compare each nonnegative Euler logarithm with the corresponding negative "
                    + "power using the uniform denominator at two. Summability follows from "
                    + "the power series. Including composite integers enlarges the tail, and "
                    + "the decreasing power function bounds that tail by its improper integral.")),
                Paragraph(Text(
                    "This result controls only omitted prime directions. It does not identify "
                    + "a finite divisor-window error, bound finite Fibonacci exponent truncations, "
                    + "or prove the resulting quantified epsilon convergence statement."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula s = F.Id("s");
        Formula x = F.Id("X");
        Formula p = F.Id("p");
        Formula negativeS = F.Seq(F.Minus, s);
        Formula summand = F.Seq(F.Minus, F.Log, F.Open,
            F.D(1), F.Minus, Power(p, negativeS), F.Close);
        Formula tail = F.Seq(F.Sum, F.Underscore,
            F.Grp(p, F.Sp, F.InMacro, F.Sp, F.Mathbb, F.Grp(F.Id("P")),
                F.Comma, F.Sp, x, F.Lt, p), F.Sp, summand);
        Formula bound = F.Seq(
            new Formula.Fraction(F.D(1),
                F.Seq(F.D(1), F.Minus, Power(F.D(2), negativeS))),
            F.Sp, F.Cdot, F.Sp,
            new Formula.Fraction(Power(x, F.Seq(F.D(1), F.Minus, s)),
                F.Seq(s, F.Minus, F.D(1))));
        return F.Disp(F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.Sp,
            F.Forall, F.Sp, x, F.InMacro, F.Mathbb, F.Grp(F.Id("N")), F.Comma, F.Sp,
            F.Open, F.D(1), F.Lt, s, F.Sp, F.Land, F.Sp, F.D(2), F.Leq, F.Sp, x, F.Close,
            F.Sp, F.Implies, F.Sp, tail, F.Sp, F.Leq, F.Sp, bound));
    }

    private static Formula Power(Formula basis, Formula exponent) =>
        new Formula.Power(basis, exponent);
}
