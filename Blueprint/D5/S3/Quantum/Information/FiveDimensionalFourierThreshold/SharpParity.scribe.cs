using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold;

internal sealed class SharpParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd Fourier matrix is an involution. The two paired sectors give explicit complex Hermitian quadratic form estimates.",
        H("Weighted coercivity on reflection-odd coordinates"),
        Blocks(
            Describe.Lean(DescribeId.Create("five-sharp-oddfourier-involutive"),
                DeclarationHandle.Create(Prefix + "oddFourier_involutive"), H("The odd Fourier matrix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real two-coordinate matrix built from σ and h squares to the identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-oddrayleigh-fourier"),
                DeclarationHandle.Create(Prefix + "oddRayleigh_fourier"), H("Rayleigh form under the Fourier involution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugation by the odd Fourier matrix reverses the centered projection operator."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-odd-weighted-coercivity"),
                DeclarationHandle.Create(Prefix + "odd_weighted_coercivity"), H("Quantitative weighted coercivity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The weighted residual in both odd coordinates plus twice the mass of the positive sector and 0.0002 times the mass of the negative sector is at most 4c times the joint odd deficit. Rational brackets certify the two Hermitian forms."))), DescribeRole.Theorem)),
        []));
}
