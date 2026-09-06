using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.FourierReadout;

internal sealed class WindowPaperFTReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Applies Mathlib Cauchy-Schwarz to the identified representer. The conclusion is uniform in the real frequency coordinate and requires no additional Fourier identification premise.",
        H("WindowPaperFTReadout"),
        Blocks(
            Describe.Lean(DescribeId.Create("item-1"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/WindowPaperFTReadout.WindowL2"), H("Standard window Hilbert space"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An abbreviation for Mathlib Lp with exponent two and Lebesgue measure restricted to the closed interval. No new norm or measure is defined."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("item-2"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/WindowPaperFTReadout.windowKernel"), H("Actual Fourier representer"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Constructs the square-integrable conjugate of exp(I*z*x). This is the representer of the existing positive-exponential paperFT, with ordinary Lebesgue normalization."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("item-3"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/WindowPaperFTReadout.window_fourier_integrable"), H("Actual integral is integrable"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Derives integrability of the zero-extended complex Fourier integrand from Mathlib L2 inner-product integrability. No smoothness or evenness is needed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("item-4"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/WindowPaperFTReadout.paperFT_window_eq_inner"), H("Identify the existing Fourier integral"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Proves exact equality between Zeta23.paperFT of a zero-extended L2 representative and the actual Hilbert inner product. The equality is derived rather than assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("item-5"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/WindowPaperFTReadout.paperFT_eq_inner_toLp"), H("Existing supported functions enter directly"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transfers a supplied square-integrable, window-supported function to the same L2 representer and the original paperFT integral, accounting for the almost-everywhere quotient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("item-6"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/WindowPaperFTReadout.windowKernel_norm_sq"), H("Exact kernel norm integral"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Computes the actual squared kernel norm as the interval integral of exp(-2 Im(z) x). The sign follows the positive-exponential Fourier convention."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("item-7"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/WindowPaperFTReadout.windowKernel_norm_sq_real"), H("Exact real-frequency normalization"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a real frequency the squared norm is exactly twice the nonnegative window radius. This is not a probability-normalized measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("item-8"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/WindowPaperFTReadout.windowKernel_norm_le"), H("Closed-strip kernel bound"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reuses the existing paperFT exponential bound to prove the L2 bound sqrt(2a)*exp(ba) throughout the whole horizontal strip, including the zero-length window."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("item-9"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/WindowPaperFTReadout.paperFT_window_sub_le"), H("Actual Fourier error from L2 error"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Applies Mathlib Cauchy-Schwarz to the identified representer. The conclusion is uniform in the real frequency coordinate and requires no additional Fourier identification premise."))), DescribeRole.Theorem)),
        []));
}
