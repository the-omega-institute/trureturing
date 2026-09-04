using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class RiemannZetaDerivativeNegativeTwoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The derivative of the Riemann zeta function at negative two is determined by its value "
            + "at three.",
        H("Riemann Zeta Derivative at Negative Two"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("riemann-zeta-derivative-at-negative-two"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Asymptotics/RiemannZetaDerivativeNegativeTwo."
                    + "riemann_zeta_derivative_negative_two"),
                H("The zeta derivative at negative two"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Differentiate the Riemann zeta functional equation at s = 3. The cosine "
                            + "factor vanishes there, so the derivatives of the amplitude and of "
                            + "zeta(s) contribute zero; only the derivative of the cosine remains.")),
                    Paragraph(Text(
                        "Using Gamma(3) = 2 and the derivative of cos(pi s/2) at s = 3 gives the "
                            + "coefficient 1/(4 pi squared). The derivative of zeta(1-s) supplies "
                            + "the opposite sign, yielding the displayed identity.")),
                    Paragraph(Text(
                        "This declaration isolates the analytic identity that supports the "
                            + "source's logarithmic-curvature coefficient. The full four-term "
                            + "asymptotic is not stated because its S, c1, and c2 are not formally "
                            + "defined. Nor is the pointwise formula 1/zeta(1) = 0 asserted: in "
                            + "Mathlib the pole is represented by a finite junk value, while the "
                            + "valid cancellation statement is asymptotic."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula zetaPrime = Seq(Zeta, Apos);
        Formula numerator = Seq(Zeta, Open, D(3), Close);
        Formula denominator = Multiply(D(4), Seq(Pi, Caret, D(2)));

        return Disp(Seq(
            zetaPrime, Open, Minus, D(2), Close, Sp, Eq, Sp,
            Minus, Frac, Grp(numerator), Grp(denominator), Dot));
    }
}
