using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Characterizations;

internal sealed class VisibleGaussianMassDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Characterizations/VisibleGaussianMass.visible_gaussian_mass";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd-double-factorial power series is the visible Gaussian mass below its "
            + "natural square-root scale.",
        H("Visible Gaussian Mass"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("visible-gaussian-mass"),
                DeclarationHandle.Create(Declaration),
                H("The visible mass has a Gaussian integral form"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive real x, the power series with coefficient "
                            + "1/(2n+1)!! equals exp(x/2)/sqrt(x) times the Gaussian "
                            + "integral from zero to sqrt(x).")),
                    Paragraph(Text(
                        "The proof differentiates u(1-u^2)^(n+1) to obtain the beta-integral "
                            + "coefficient recurrence, solves that recurrence using Mathlib's "
                            + "double factorial identities, and exchanges the exponential "
                            + "series with the interval integral by dominated convergence.")),
                    Paragraph(Text(
                        "The final substitution t=sqrt(x)u gives the displayed scale factor. "
                            + "The positivity premise keeps the displayed quotient away from "
                            + "its removable singularity at x=0. The later tail completion and "
                            + "continued-fraction discussion are outside the named theorem."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula x = F.Id("x");
        Formula n = F.Id("n");
        Formula t = F.Id("t");
        Formula sqrtX = F.Seq(F.Sqrt, F.Grp(x));
        Formula index = F.Seq(F.D(2), n, F.Plus, F.D(1));
        Formula summand = new Formula.Fraction(
            new Formula.Power(x, n),
            F.Seq(F.Grp(index), F.Bang, F.Bang));
        Formula series = F.Seq(
            F.Sum, F.Underscore, F.Grp(n, F.Eq, F.D(0)),
            F.Caret, F.Grp(F.Infty), F.Sp, summand);
        Formula exponentialScale = F.Seq(
            F.Exp, F.Grp(new Formula.Fraction(x, F.D(2))));
        Formula gaussian = F.Seq(
            F.Exp, F.Grp(new Formula.Fraction(
                F.Seq(F.Minus, new Formula.Power(t, F.D(2))),
                F.D(2))));
        Formula integral = F.Seq(
            F.Int, F.Underscore, F.Grp(F.D(0)), F.Caret, F.Grp(sqrtX), F.Sp,
            gaussian, F.Thin, F.Id("dt"));

        return F.Disp(F.Seq(
            F.Forall, F.Sp, x, F.Sp, F.InMacro, F.Sp, reals, F.Comma, F.RowBreak,
            F.D(0), F.Sp, F.Lt, F.Sp, x, F.Sp, F.Rightarrow, F.Sp,
            series, F.Sp, F.Eq, F.Sp,
            new Formula.Fraction(exponentialScale, sqrtX), F.Sp, F.Cdot, F.Sp,
            integral, F.Dot));
    }
}
