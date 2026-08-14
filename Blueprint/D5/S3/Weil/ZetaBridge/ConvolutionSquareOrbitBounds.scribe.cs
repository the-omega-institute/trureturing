using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ConvolutionSquareOrbitBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex-frequency convolution-square factorization gives an energy bound for every "
            + "off-line four-point zero orbit, without assigning an off-line sign.",
        H("Convolution-Square Orbit Energy Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complex-frequency-convolution-square-factorization"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds."
                        + "fourierLaplace_convolutionSquare_complex"),
                H("Complex-frequency convolution-square factorization"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("g"), InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
                    Forall, Sp, F.Id("z"), InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Operatorname, Grp(F.Id("fourierLaplace")), Sp,
                    Operatorname, Grp(F.Id("convolutionSquare")), Open, F.Id("g"), Close,
                    Open, F.Id("z"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("fourierLaplace")), Sp, F.Id("g"), Sp,
                    Open, F.Id("z"), Close, Cdot, Sp,
                    Overline, Grp(Operatorname, Grp(F.Id("fourierLaplace")), Sp, F.Id("g"), Sp,
                        Open, Overline, F.Id("z"), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Twist g and its Weil involution by the complex exponential kernel. "
                        + "The kernel is multiplicative under addition, so the twisted convolution "
                        + "is the kernel times convolutionSquare g. Mathlib's integral_convolution "
                        + "then factors the integral, and fourierLaplace_involution_conj identifies "
                        + "the second factor with the conjugated transform at the conjugate frequency."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("off-line-orbit-real-value-has-energy-bounds"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds."
                        + "off_line_zero_orbit_sum_energy_bounds"),
                H("An off-line orbit real value is bounded by transform energy"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Z"), Colon, Sp,
                    Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
                    F.Id("g"), InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
                    F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("Z"), Dot, F.Id("conjugation"), Open, F.Id("n"), Close,
                    Sp, Neq, Sp, F.Id("n"), Sp, Land, Sp,
                    Re, Open, F.Id("Z"), Dot, F.Id("zero"), Open, F.Id("n"), Close, Close,
                    Sp, Neq, Sp, Operatorname, Grp(F.Id("criticalAbscissa")), Sp,
                    Rightarrow, Sp,
                    Neg, Open, F.Id("energyBound"), Close, Sp, Leq, Sp,
                    Re, Open, Operatorname, Grp(F.Id("orbitSum")), Open,
                    F.Id("Z"), Comma, F.Id("g"), Comma, F.Id("n"), Close, Close,
                    Sp, Land, Sp,
                    Re, Open, Operatorname, Grp(F.Id("orbitSum")), Open,
                    F.Id("Z"), Comma, F.Id("g"), Comma, F.Id("n"), Close, Close,
                    Sp, Leq, Sp, F.Id("energyBound"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The four-point orbit identity makes the orbit total four times the real part "
                        + "of one multiplicity-weighted summand. Factorization writes its transform "
                        + "as A times the conjugate of B, with A and B evaluated at gamma and its "
                        + "conjugate. Complex.normSq_add and Complex.normSq_sub give the two-sided "
                        + "AM-GM estimate, yielding energyBound = 2 times multiplicity times "
                        + "(normSq A + normSq B). This records no sign or positivity for off-line terms."))),
                DescribeRole.Theorem))));
}
