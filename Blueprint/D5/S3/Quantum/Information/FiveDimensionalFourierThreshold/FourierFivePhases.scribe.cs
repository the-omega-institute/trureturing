using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold;

internal sealed class FourierFivePhasesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFivePhases.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The five-point kernel is the standard additive character evaluated at the product of the two residue indices.",
        H("Exact pentagon phase sums"),
        Blocks(
            Describe.Lean(DescribeId.Create("five-fourier-pentagonphase-small-sum"),
                DeclarationHandle.Create(Prefix + "pentagonPhase_small_sum"), H("Two and three pentagon terms"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two distinct terms have sum of modulus at most the golden ratio by the repository pentagon cosine identities. Three terms reduce to two by the vanishing sum of all five phases."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-fourier-kernel-five-eq-pentagonphase"),
                DeclarationHandle.Create(Prefix + "kernel_five_eq_pentagonPhase"), H("The Fourier kernel as a fifth-root phase"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The five-point kernel is the standard additive character evaluated at the product of the two residue indices."))), DescribeRole.Theorem)),
        []));
}
