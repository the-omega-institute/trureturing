using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold;

internal sealed class TwoBasisMasksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/TwoBasisMasks.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The small-mask upper Gram bound bounds the mass of complementary large masks from below. The balanced lower Gram bound makes the square synthesis map invertible and gives the balanced mass gap through its adjoint.",
        H("From synthesis Gram bounds to measurement mass gaps"),
        Blocks(
            Describe.Lean(DescribeId.Create("five-fourier-basislaw"),
                DeclarationHandle.Create(Prefix + "basisLaw"), H("The two Born probability tables"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each row is the squared modulus of the inner product with a vector in one of the two orthonormal bases."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-fourier-masksynthesis"),
                DeclarationHandle.Create(Prefix + "maskSynthesis"), H("Synthesis on a selected set of basis columns"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The synthesis map sends the coordinate of each retained row to its basis vector. Its adjoint reads the corresponding amplitude."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-fourier-spectralmaskgaps-of-synthesis"),
                DeclarationHandle.Create(Prefix + "spectralMaskGaps_of_synthesis"), H("Mass gaps from two Gram bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The small-mask upper Gram bound bounds the mass of complementary large masks from below. The balanced lower Gram bound makes the square synthesis map invertible and gives the balanced mass gap through its adjoint."))), DescribeRole.Theorem)),
        []));
}
