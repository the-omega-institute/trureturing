using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class WindowDiffractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Fourier/WindowDiffraction",
            "The Fourier amplitude of a finite interval window is an exact sine kernel, specializing at golden-window length to the diffraction closed form."),
        H("Golden-Window Fourier Diffraction"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("a-finite-interval-window-has-exact-sine-kernel-amplitude"),
                H("A finite interval window has exact sine-kernel amplitude"),
                LeanTheorem("D5/S3/Fourier/WindowDiffraction.window_fourier_amplitude"),
                Disp(Seq(
                    Bar, Widehat, Sp, F.Id("c"), Underscore, Grp(F.Id("m")), Open, Ell, Close, Bar,
                    Eq,
                    Frac,
                    Grp(Bar, Sin, Open, Pi, Sp, F.Id("m"), Ell, Close, Bar),
                    Grp(Pi, Sp, F.Id("m")),
                    Comma, Quad, Sp, F.Id("m"), Sp, Gt, Sp, D(0), Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For a positive Fourier mode, integrating the complex exponential over the interval from zero to the window length and taking its norm gives the exact sine-kernel amplitude. The proof evaluates the exponential integral, reduces the complex norm to the sine half-angle identity, and uses positivity of the mode and pi to normalize the denominator.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-golden-window-has-the-diffraction-closed-form"),
                H("The golden window has the diffraction closed form"),
                LeanTheorem("D5/S3/Fourier/WindowDiffraction.golden_window_fourier_amplitude"),
                Disp(Seq(
                    Bar, Widehat, Sp, F.Id("c"), Underscore, Grp(F.Id("m")), Bar,
                    Eq,
                    Frac,
                    Grp(Bar, Sin, Open, Pi, Sp, F.Id("m"), Slash, Varphi, Close, Bar),
                    Grp(Pi, Sp, F.Id("m")),
                    Comma, Quad, Varphi, Eq,
                    Frac, Grp(D(1), Plus, Sqrt, Grp(D(5))), Grp(D(2)),
                    Comma, Quad, Sp, F.Id("m"), Sp, Gt, Sp, D(0), Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The cut-and-project interval window has length one over the golden ratio. Substituting this length into the general interval-window formula gives the exact diffraction amplitude |c-hat_m| = |sin(pi*m/phi)|/(pi*m), with no asymptotic approximation or omitted normalization factor.")))
            ))));
}
