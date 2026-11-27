using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class OccupiedMellinKelvinDocument : IScribeDocumentDefinition
{
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Parens(Formula x) => Seq(Left, Open, x, Right, Close);
    private static Formula Abs(Formula x) => Seq(Left, Lvert, Sp, x, Right, Rvert);
    private static Formula Pow(Formula x, Formula p) => Seq(x, Caret, Grp(p));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Half => Ratio(D(1), D(2));
    private static Formula Coefficient => F.Id("c");
    private static Formula Kernel => Seq(F.Id("K"), Underscore, Grp(Beta));
    private static Formula Y => F.Id("y");
    private static Formula KernelAtY => Seq(Kernel, Open, Y, Close);
    private static Formula Integral(Formula x) => Seq(Int, Underscore, Grp(Reals), x, Thin, F.Id("dy"));
    private static Formula J(Formula exponent) => Seq(F.Id("J"), Open, exponent, Close);

    private static Formula OnExponentRange(Formula lower, Formula consequence) =>
        Seq(Open, Forall, Sp, Beta, InMacro, Sp, Reals, Comma, Quad,
            lower, Le, Beta, Lt, D(1), Longrightarrow, Sp, consequence, Close);

    private static Formula BalanceAndGap() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        OnExponentRange(D(0), Call("Integrable", Kernel)), Sp, Land, RowBreak, Grp(),
        J(Half), Eq, D(0), Quad, Land, Quad, D(0), Lt, Coefficient, Sp, Land, RowBreak, Grp(),
        OnExponentRange(Half, Seq(Coefficient, Cdot, Sp, Parens(Seq(Beta, Minus, Half)), Le, Sp, J(Beta))),
        End, Grp(F.Id("gathered"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inversion across the unit scale pairs the real signed Mellin kernel and gives a fixed linear gain above the critical exponent.",
        H("Signed Mellin cancellation by inversion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-mellin-kernel"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedMellinKelvin.signedKernel"),
                H("Signed power kernel"),
                StatementSource.FromAuthor(Disp(Seq(KernelAtY, Eq,
                    Parens(Seq(Pow(Abs(Y), Seq(Minus, Beta)), Minus, D(1))),
                    Cdot, Sp, Pow(Abs(Seq(D(1), Minus, Y)), Seq(Minus, Ratio(D(3), D(2))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exponent beta and position y are real. The powers are real powers. Values on the singular points do not affect Lebesgue integration."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signed-mellin-integral"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedMellinKelvin.J"),
                H("Whole-line Mellin integral"),
                StatementSource.FromAuthor(Disp(Seq(J(Beta), Eq, Integral(KernelAtY)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integration is over the entire real line with Lebesgue measure, not just its positive half. The theorem below proves integrability on the stated exponent range."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kelvin-gap-coefficient"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedMellinKelvin.gapCoefficient"),
                H("Fixed coefficient of the lower bound"),
                StatementSource.FromAuthor(Disp(Seq(Coefficient, Eq, Ratio(
                    Seq(Parens(Seq(D(1), Minus, Exp, Parens(Seq(Minus, Ratio(Seq(Log, Sp, D(2)), D(2)))))),
                        Cdot, Sp, Log, Sp, D(2)), D(4))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coefficient is independent of beta. The factor one quarter is the length of the compact interval used for the lower estimate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("critical-cancellation-and-linear-gap"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/OccupiedMellinKelvin.signed_mellin_cancellation_and_gap"),
                H("Exact cancellation and a positive linear gap"),
                StatementSource.FromAuthor(BalanceAndGap()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Integrable means absolutely integrable with respect to Lebesgue measure. Near zero the bound is a multiple of the absolute position to the power minus beta. Near one the numerator vanishes linearly, leaving an integrable power minus one half. Both tails are controlled by the power minus three halves.")),
                    Paragraph(Text(
                        "Substituting the reciprocal where the absolute position exceeds one contributes the absolute Jacobian. After factoring the paired kernel, its numerator at absolute position t is the product of one minus t to the beta and t to the minus beta minus t to the minus one half. This vanishes at the critical exponent and is nonnegative throughout the supercritical range. A positive lower estimate on the interval from one quarter to one half gives the displayed uniform linear bound."))),
                DescribeRole.Theorem))));
}
