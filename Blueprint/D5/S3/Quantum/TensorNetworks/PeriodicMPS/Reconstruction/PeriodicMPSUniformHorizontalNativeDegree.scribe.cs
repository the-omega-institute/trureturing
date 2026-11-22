using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformHorizontalNativeDegreeDocument : IScribeDocumentDefinition
{
    private const string Title = "Ambient degree of the literal Pauli readout";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontalnativedegree-ambientmoment-totaldegree-le-eight"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHorizontalNativeDegree.ambientMoment_totalDegree_le_eight"),
                H("Degree of the native transfer moments"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The aligned word expansion bounds the ambient moment for each of the eight powers used by the Hermite remainder."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontalnativedegree-ambientpartial-totaldegree-le-seven"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHorizontalNativeDegree.ambientPartial_totalDegree_le_seven"),
                H("Degree of ambient partials"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Differentiation reduces the degree budget by one."))),
                DescribeRole.Theorem))));
}
