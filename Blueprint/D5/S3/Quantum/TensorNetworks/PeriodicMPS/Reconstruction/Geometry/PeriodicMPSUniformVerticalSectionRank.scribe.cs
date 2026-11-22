using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformVerticalSectionRankDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalSectionRank";
    private const string Title = "Triplet and singlet determinant tests on the generic section";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformverticalsectionrank"),
                DeclarationHandle.Create(Module + ".no_divisor_of_genericSectionMinors"),
                H("Generic section minors exclude a noncoordinate divisor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For m at least three, a prime root divisor avoiding the trace sum and the four coordinates cannot make both section minors vanish for every admissible pairing."))),
                DescribeRole.Theorem))));
}
