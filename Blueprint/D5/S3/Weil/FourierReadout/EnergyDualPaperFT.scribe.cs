using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.FourierReadout;

internal sealed class EnergyDualPaperFTDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Fourier readouts and their limit are certified through energy-direction trial residuals.",
        H("Energy-Dual Paper Fourier Transform"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-fourier-error"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/EnergyDualPaperFT.rayleigh_paperFT_dual_error"), H("Actual Fourier directional error"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Substitutes the existing constructed paperFT kernel into the full-domain Rayleigh dual certificate. The sensitivity is an expression in the trial, actual shifted action and full residual. The Fourier integral is the original Zeta23.paperFT with its positive-exponential convention."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-fourier-nonzero"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/EnergyDualPaperFT.rayleigh_paperFT_dual_nonzero"), H("Energy-certified nonzero actual readout"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A strict directional error margin excludes a zero of the actual eigenvector Fourier transform at the specified frequency. This is a sufficient condition, without claiming a norm-ball necessity or a zero count."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("directional-limit-transfer"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/EnergyDualPaperFT.rayleigh_paperFT_dual_uniform_limit"), H("Directional-rate limit transfer"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given actual varying-domain Rayleigh conditions, a scalar envelope for the residual-based coefficients and the rate |c_j| squared times B_j times (U_j-ell_j) tending to zero, transfers the correctly normalized candidate Fourier limit on any target set to the actual projective eigenmodes. The rate, arithmetic operator conditions and candidate limit remain explicit inputs. No global strip-kernel norm factor or exact inverse is imposed."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/FourierReadout/WindowPaperFTReadout")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaLinear/ProjectiveEnergyDual"))]));
}
