using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GoldenGermThirdOrderLedgerDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderLedger."
            + "golden_third_normalized_factor_deviation_norm_summable";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit third-order golden ledger cancels every local mode below phi to the "
            + "fifth power and leaves a prime-summable normalized deviation.",
        H("Golden Germ Third-Order Ledger"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-third-order-ledger"),
            DeclarationHandle.Create(Declaration),
            H("Third-order local cancellation reaches the phi-fifth boundary"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The proof computes beta at modes four and five: mode four has weight "
                        + "two phi-squared plus phi-cubed, while mode five has weight exactly "
                        + "phi to the fifth power. Splitting after six modes isolates the "
                        + "remaining tail.")),
                Paragraph(Text(
                    "The frozen golden_germ_second_order_factorization gives the global "
                        + "factorization and its unique continuation, but does not expose the "
                        + "local normalized remainder needed here. This ledger instead reuses "
                        + "the canonical definitions germLocalFactor and o5Beta, together with "
                        + "o5_beta_zero, o5_beta_power_law, o5_beta_closed_form, and "
                        + "o5_beta_growth, and proves the local identity independently from the "
                        + "six-mode expansion. Its displayed factors cancel minus y-squared and "
                        + "plus x-squared y; the first retained monomial x y-squared lies exactly "
                        + "on the threshold, and the tail starts there and grows linearly.")),
                Paragraph(Text(
                    "This is the next local extraction step on the golden Euler germ staircase "
                        + "used in OACTC parts 580 and 581 and on the RH-route O-5 control line. "
                        + "It advances the absolute-summability boundary to real part greater "
                        + "than one over phi to the fifth power. It does not assert O-5, a "
                        + "global continuation or nonvanishing theorem, or the Riemann "
                        + "Hypothesis."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenLocalFactor")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula thresholdFifth = Fraction(F.D(1), Power(F.Varphi, F.D(5)));
        Formula xAtP = Call("x", p);
        Formula yAtP = Call("y", p);
        Formula xDefinition = F.Seq(
            xAtP, F.Sp, F.Colon, F.Eq, F.Sp,
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared)));
        Formula yDefinition = F.Seq(
            yAtP, F.Sp, F.Colon, F.Eq, F.Sp,
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp, phiCubed)));
        Formula normalized = NormalizedFactor(s, p, xAtP, yAtP);
        Formula absoluteConvergence = Call("Summable", F.Seq(
            p, F.Colon, F.Sp, Call("Primes", NaturalNumbers()),
            F.Sp, F.Mapsto, F.Sp,
            F.Lvert, normalized, F.Sp, F.Minus, F.Sp, F.D(1), F.Rvert));

        return F.Disp(new Formula.Aligned([
            F.Seq(F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma),
            F.Seq(
                thresholdFifth, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
                F.Sp, F.Rightarrow),
            F.Seq(
                xDefinition, F.Comma, F.Sp, yDefinition, F.Comma, F.Sp,
                absoluteConvergence, F.Dot),
        ]));
    }

    private static Formula NormalizedFactor(
        Formula s,
        Formula p,
        Formula x,
        Formula y)
    {
        Formula oneMinusYSquared = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp, Power(y, F.D(2)), F.Close);
        Formula oneMinusXSquaredY = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(x, F.D(2)), F.Sp, F.Times, F.Sp, y, F.Close);
        Formula oneMinusY = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp, y, F.Close);
        Formula onePlusX = F.Seq(
            F.Open, F.D(1), F.Sp, F.Plus, F.Sp, x, F.Close);

        return F.Seq(
            Power(oneMinusYSquared, F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp, oneMinusXSquaredY,
            F.Sp, F.Times, F.Sp, oneMinusY,
            F.Sp, F.Times, F.Sp,
            Power(onePlusX, F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp, LocalFactor(s, p));
    }

    private static Formula LocalFactor(Formula s, Formula p) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(F.Id("v"), F.InMacro, F.Sp, NaturalNumbers()),
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp,
                Call("o5Beta", F.Id("v")))));

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

    private static Formula NaturalNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq(pieces.ToArray());
    }
}
