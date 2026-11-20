using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteLocalGraphsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct cubic germs in the six-site raw readout",
        H("Distinct cubic germs in the six-site raw readout"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsitelocalgraphs-normal-germs-ne"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteLocalGraphs.normal_germs_ne"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The two normal graphs over the common raw tangent coordinates have different cubic terms in the selected off-diagonal direction."))), DescribeRole.Theorem))));
}
