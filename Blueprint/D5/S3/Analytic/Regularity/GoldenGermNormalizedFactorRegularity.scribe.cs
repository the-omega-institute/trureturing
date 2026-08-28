using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Regularity;

internal sealed class GoldenGermNormalizedFactorRegularityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Regularity/GoldenGermNormalizedFactorRegularity."
            + "golden_germ_normalized_factor_regularity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cancellation makes the normalized golden germ product holomorphic above one over "
            + "phi cubed and continuous at one over phi squared.",
        H("Golden Germ Normalized Factor Regularity"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-normalized-factor-regularity"),
            DeclarationHandle.Create(Declaration),
            H("The normalized golden germ factor is regular at the zeta boundary"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For each real sigma strictly above one over phi cubed, the proof "
                        + "constructs a prime-indexed summable majorant. It bounds the "
                        + "normalized local-factor deviation simultaneously for every "
                        + "complex s with real part greater than sigma.")),
                Paragraph(Text(
                    "The local golden series is split into its vacuum term, its first "
                        + "excited mode p^(-s phi^2), and the tail beginning at beta two. "
                        + "Multiplication by one minus the first mode cancels the linear "
                        + "term. The remaining tail, squared first mode, and their product "
                        + "are dominated by summable families at sigma.")),
                Paragraph(Text(
                    "Each fixed-prime local series is holomorphic on the same half-plane. "
                        + "Pinned Mathlib's locally uniform infinite-product theorem applies "
                        + "to the uniform majorant, and finite products are holomorphic. "
                        + "The locally uniform limit is therefore holomorphic on the full "
                        + "region where the real part exceeds one over phi cubed.")),
                Paragraph(Text(
                    "Since one over phi squared is strictly greater than one over phi "
                        + "cubed, it is an interior point of this holomorphy region. The "
                        + "displayed ContinuousAt conclusion follows from the regional "
                        + "continuity, rather than from pointwise summability alone.")),
                Paragraph(Text(
                    "STOPPING JUSTIFICATION: this theorem supplies the regularity input "
                        + "isolated by GoldenGermZetaBoundary, but it does not itself state "
                        + "the downstream singularity conclusion for the continued germ. "
                        + "That conclusion requires a distinct theorem combining this "
                        + "continuity with the frozen boundary identity, transported zeta "
                        + "residue, and nonvanishing. No convergence or regularity at or to "
                        + "the left of one over phi cubed is asserted."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula sigma = F.Id("sigma");
        Formula p = F.Id("p");
        Formula u = F.Id("u");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula thresholdSquared = Fraction(F.D(1), phiSquared);
        Formula thresholdCubed = Fraction(F.D(1), Power(F.Varphi, F.D(3)));
        Formula primes = Call("Primes", NaturalNumbers());
        Formula local = LocalFactor(s, p);
        Formula normalized = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared)),
            F.Close, F.Sp, F.Times, F.Sp, local);
        Formula gAtS = Call("G", s);
        Formula gDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            gAtS, F.Sp, F.Colon, F.Eq, F.Sp, PrimeProduct(normalized));
        Formula region = F.Seq(
            F.OpenBrace, s, F.InMacro, F.Sp, ComplexNumbers(), F.Sp, F.Mid, F.Sp,
            thresholdCubed, F.Sp, F.Lt, F.Sp,
            F.Re, F.Open, s, F.Close, F.CloseBrace);
        Formula deviationBound = F.Seq(
            new Formula.Norm(F.Seq(
                normalized, F.Sp, F.Minus, F.Sp, F.D(1))),
            F.Sp, F.Leq, F.Sp, Call("u", p));
        Formula pointwiseBound = F.Seq(
            F.Forall, F.Sp, p, F.InMacro, F.Sp, primes, F.Comma, F.Sp,
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            sigma, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp, deviationBound);
        Formula majorant = F.Seq(
            F.Forall, F.Sp, sigma, F.InMacro, F.Sp, RealNumbers(), F.Comma, F.Sp,
            thresholdCubed, F.Sp, F.Lt, F.Sp, sigma,
            F.Sp, F.Rightarrow, F.Sp,
            F.Exists, F.Sp, u, F.Colon, F.Sp, primes, F.Sp, F.To, F.Sp,
            RealNumbers(), F.Comma, F.Sp,
            Call("Summable", u), F.Sp, F.Land, F.Sp, pointwiseBound);
        Formula continuityOn = Call("ContinuousOn", F.Id("G"), region);
        Formula continuityAt = Call("ContinuousAt", F.Id("G"), thresholdSquared);
        Formula analyticOn = Call(
            "AnalyticOnNhd", ComplexNumbers(), F.Id("G"), region);

        return F.Disp(new Formula.Aligned([
            F.Seq(F.Id("G"), F.Colon, F.Sp, ComplexNumbers(), F.Sp, F.To, F.Sp,
                ComplexNumbers(), F.Comma),
            F.Seq(gDefinition, F.Comma),
            F.Seq(F.Open, majorant, F.Close, F.Sp, F.Land),
            F.Seq(continuityOn, F.Sp, F.Land),
            F.Seq(continuityAt, F.Sp, F.Land),
            F.Seq(analyticOn, F.Dot),
        ]));
    }

    private static Formula LocalFactor(Formula s, Formula p) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(F.Id("v"), F.InMacro, F.Sp, NaturalNumbers()),
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp,
                Call("o5Beta", F.Id("v")))));

    private static Formula PrimeProduct(Formula body) =>
        F.Seq(
            F.Prod, F.Underscore,
            F.Grp(F.Id("p"), F.InMacro, F.Sp, Call("Primes", NaturalNumbers())),
            body);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

    private static Formula RealNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("R")));

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
