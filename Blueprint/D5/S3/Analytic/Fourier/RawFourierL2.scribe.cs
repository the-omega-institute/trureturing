using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class RawFourierL2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Fourier/RawFourierL2.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integral and L² Fourier transforms agree for integrable square-integrable complex functions on the real line, in Mathlib's frequency convention with kernel exp(-2*pi*i*x*xi).",
        H("Compatibility of the integral and L² Fourier transforms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("raw-fourier-ae-eq-l2"),
                DeclarationHandle.Create(Prefix + "raw_fourier_ae_eq_L2"),
                H("Almost-everywhere agreement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integral transform is continuous, and the L² transform is locally integrable. Pairing with compactly supported smooth tests gives the same integrals by Fourier duality and Mathlib's identification of the L² transform with the tempered-distribution transform. The test integrals imply almost-everywhere equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-fourier-elpnorm-eq"),
                DeclarationHandle.Create(Prefix + "raw_fourier_eLpNorm_eq"),
                H("Preservation of the L² seminorm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Almost-everywhere agreement transfers the seminorm to the L² transform, where the Fourier linear isometry preserves it."))),
                DescribeRole.Theorem))));
}
