using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.HeatLayers;

internal sealed class GoldenHeatMidlineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden heat spectrum has a single exact line selected by reflection, half-density unitarity, square summability, and self-resonance.",
        H("The Sixfold Golden Heat Midline"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-heat-spectrum-has-the-sixfold-midline"),
                DeclarationHandle.Create(
                    "D5/S3/Midline/HeatLayers/GoldenHeatMidline.golden_heat_sixfold_midline"),
                H("The golden heat spectrum has the sixfold midline"),
                StatementSource.FromAuthor(SixfoldFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Conjugate reflection and coordinatewise unit modulus after the canonical "
                        + "half-density normalization select real part one over twice phi squared. "
                        + "The labeled coefficient vector is constructed directly from the frozen "
                        + "golden spectrum and its exact square-summability proof; its squared norm "
                        + "is the heat trace at twice the real parameter and is independent of the "
                        + "vertical coordinate.")),
                    Paragraph(Text(
                        "Boundary divergence of the ground prime layer supplies the strict L2 iff. "
                        + "The resonance equation selects the same self-line and identifies every "
                        + "parameter's unique partner as one over phi squared minus its conjugate.")),
                    Paragraph(Text(
                        "The numerical window checks attached to the source are empirical evidence "
                        + "outside the named theorem and are not encoded as deductive clauses."))),
                DescribeRole.Theorem))));

    private static Formula SixfoldFormula()
    {
        Formula s = F.Id("s");
        Formula w = F.Id("w");
        Formula a = F.Id("a");
        Formula sigma = SigmaLower;
        Formula t = F.Id("t");
        Formula alpha = Seq(Frac, Grp(D(1)), Grp(Varphi, Caret, Grp(D(2))));
        Formula halfAlpha = Seq(Frac,
            Grp(D(1)), Grp(D(2), Varphi, Caret, Grp(D(2))));
        Formula conjugateS = Seq(Overline, Grp(s));
        Formula spectrum = Seq(Operatorname, Grp(F.Id("goldenSpectrum")));
        Formula coefficient = Seq(Operatorname, Grp(F.Id("heatCoefficient")));
        Formula halfDensity = Seq(Operatorname, Grp(F.Id("halfDensityCoefficient")));
        Formula resonant = Seq(Operatorname, Grp(F.Id("KernelResonant")));
        Formula z = Seq(Mathbf, Grp(F.Id("Z")), Underscore, Grp(F.Id("gold")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open, Forall, Sp, s, InMacro, Mathbb, Grp(F.Id("C")), Comma, Sp,
            s, Eq, alpha, Minus, conjugateS, Sp, Leftrightarrow, Sp,
            Re, Open, s, Close, Eq, halfAlpha, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, s, InMacro, Mathbb, Grp(F.Id("C")), Comma, Sp,
            Open, Forall, Sp, a, Comma, Sp,
            Bar, halfDensity, Open, spectrum, Comma, alpha, Comma, s, Comma, a, Close,
            Bar, Eq, D(1), Close, Sp, Leftrightarrow, Sp,
            Re, Open, s, Close, Eq, halfAlpha, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, sigma, Comma, t, InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp,
            halfAlpha, Lt, sigma, Sp, Rightarrow, Sp,
            Operatorname, Grp(F.Id("let")), Sp, z, Sp, Colon, Eq, Sp,
            coefficient, Open, spectrum, Comma, Sp,
            sigma, Plus, F.Id("i"), t, Close, Semi, Sp,
            Left, Vert, z, Right, Vert,
            Caret, Grp(D(2)), Eq,
            Operatorname, Grp(F.Id("heatTrace")), Open, spectrum, Comma, D(2), sigma, Close,
            Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, s, InMacro, Mathbb, Grp(F.Id("C")), Comma, Sp,
            Operatorname, Grp(F.Id("MemLp")), Open,
            coefficient, Open, spectrum, Comma, s, Close, Comma, D(2), Close,
            Sp, Leftrightarrow, Sp, halfAlpha, Lt, Re, Open, s, Close, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, s, InMacro, Mathbb, Grp(F.Id("C")), Comma, Sp,
            resonant, Open, alpha, Comma, s, Comma, s, Close,
            Sp, Leftrightarrow, Sp, Re, Open, s, Close, Eq, halfAlpha, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, s, Comma, w, InMacro, Mathbb, Grp(F.Id("C")), Comma, Sp,
            resonant, Open, alpha, Comma, s, Comma, w, Close,
            Sp, Leftrightarrow, Sp, w, Eq, alpha, Minus, conjugateS, Close,
            Dot, Sp, End, Grp(F.Id("gathered"))));
    }
}
