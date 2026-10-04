using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.RenyiDivergence;

internal sealed class UniformPowerSlopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Power difference quotients converge uniformly on bounded nonnegative spectra, including zero.",
        H("Uniform Power Slope"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-power-slope"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/RenyiDivergence/UniformPowerSlope.rpow_slope_tendsto_uniformly"),
                H("A common error bound through the zero eigenvalue"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(
                    Paragraph(Text(
                        "For every real upper bound K and every epsilon greater than zero, "
                        + "there exists delta greater than zero such that every real h with "
                        + "0 < abs(h) < delta and every x in [0,K] satisfy the displayed bound. "
                        + "The logarithm is natural. The interval may be empty; the zero "
                        + "endpoint is included, with x log x equal to zero there.")),
                    Paragraph(Text(
                        "The proof uses a common exponential majorant near zero and a "
                        + "uniform exponential remainder estimate on the remaining compact "
                        + "positive interval. The same delta controls both signs of h. "
                        + "No lower positive spectral bound or state dimension assumption "
                        + "is imposed.")),
                    Paragraph(Text(
                        "This attributed Physlib port supplies a supporting analytic estimate "
                        + "for singular matrix relative-entropy limits. The variable-base "
                        + "trace limit, noncommutative data processing, quantum Pinsker and "
                        + "thermal recovery remain separate mathematical obligations."))),
                DescribeRole.Theorem))));

    private static Formula Statement() => Disp(Seq(
        Forall, Sp, F.Id("K"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
        Forall, Sp, Varepsilon, Comma, Sp, D(0), Sp, Lt, Sp, Varepsilon, Sp,
        Rightarrow, Sp, Exists, Sp, DeltaLower, Comma, Sp,
        D(0), Sp, Lt, Sp, DeltaLower, Sp, Land, Sp,
        Forall, Sp, F.Id("h"), Comma, Sp,
        Open, D(0), Sp, Lt, Sp, Lvert, Sp, F.Id("h"), Rvert, Sp, Land, Sp,
        Lvert, Sp, F.Id("h"), Rvert, Sp, Lt, Sp, DeltaLower, Close, Sp, Rightarrow, Sp,
        Forall, Sp, F.Id("x"), Sp, InMacro, Sp,
        OpenBracket, D(0), Comma, Sp, F.Id("K"), CloseBracket, Comma, Sp,
        Lvert, Frac, Grp(F.Id("x"), Caret, Grp(D(1), Plus, F.Id("h")), Minus, F.Id("x")),
        Grp(F.Id("h")), Minus, F.Id("x"), Sp, Log, Sp, F.Id("x"), Rvert,
        Sp, Lt, Sp, Varepsilon));
}
