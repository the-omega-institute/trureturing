using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold;

internal sealed class FourierFiveBasisDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveBasis.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Splitting the sum over the two bases gives the computational readout and the inverse-QFT readout.",
        H("Coordinate and Fourier Born laws"),
        Blocks(
            Describe.Lean(DescribeId.Create("five-fourier-fourierbasis"),
                DeclarationHandle.Create(Prefix + "fourierBasis"), H("The normalized Fourier orthonormal basis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The basis columns use the repository QFT. Their coordinate map is the inverse QFT, which preserves the Euclidean norm."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-fourier-fourierbasis-entry"),
                DeclarationHandle.Create(Prefix + "fourierBasis_entry"), H("The normalized Fourier kernel entry"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Applying the QFT to a coordinate unit vector selects a single normalized kernel value."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-fourier-fivescore-eq-sum"),
                DeclarationHandle.Create(Prefix + "fiveScore_eq_sum"), H("The two five-row score sums"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Splitting the sum over the two bases gives the computational readout and the inverse-QFT readout."))), DescribeRole.Theorem)),
        []));
}
