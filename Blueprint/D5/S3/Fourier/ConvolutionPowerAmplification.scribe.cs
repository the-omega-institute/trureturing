using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class ConvolutionPowerAmplificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repeated convolution turns a strictly separated side packet into a negligible term.",
        H("Convolution Power Amplification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("double-centered-convolution-power-amplification"),
                DeclarationHandle.Create(
                    "D5/S3/Fourier/ConvolutionPowerAmplification."
                        + "double_centered_convolution_power_amplification"),
                H("The normalized double-centered packet tends to one"),
                StatementSource.FromAuthor(AmplificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The iteration indexed by n contains exactly n+1 convolution factors. "
                            + "Its Fourier-Laplace transform is the corresponding n+1 power, "
                            + "without introducing a zero-fold compactly supported identity.")),
                    Paragraph(Text(
                        "The cosine-modulated inverse packet has transform B_(n+1), remains "
                            + "smooth and even, and has support in (-(n+1), n+1) when the source "
                            + "test has support in (-1, 1). Real-valuedness is also preserved.")),
                    Paragraph(Text(
                        "At t+i delta, the main summand is q0^(n+1). The strict norm bound on "
                            + "the other shifted transform makes its ratio to q0 have norm below "
                            + "one, so the normalized side power tends to zero."))),
                DescribeRole.Theorem))));

    private static Formula AmplificationFormula() => Disp(Seq(
        Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
        Frac,
        Grp(
            F.Id("B"), Underscore, Grp(F.Id("n"), Plus, D(1)),
            Open, F.Id("t"), Plus, F.Id("i"), Thin, F.Id("delta"), Close),
        Grp(
            F.Id("q"), Underscore, Grp(D(0)), Caret,
            Grp(F.Id("n"), Plus, D(1))),
        Sp, Eq, Sp, D(1), Dot));
}
