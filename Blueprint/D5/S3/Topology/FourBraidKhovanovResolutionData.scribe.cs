using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FourBraidKhovanovResolutionDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Checked resolution blocks for the four-braid",
        H("Checked resolution blocks for the four-braid"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-braid-resolution-block-correctness"),
                DeclarationHandle.Create("D5/S3/Topology/FourBraidKhovanovResolutionData.snapshot_correct"),
                H("The stored blocks agree with the smoothing calculation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each block of 32 smoothing choices records the maximum quantum grade. "
                    + "For a choice that can contribute at grade 17 or higher, it also records "
                    + "the circle partition. The kernel checks each block against the actual "
                    + "matching calculation, so subsequent matrix checks can reuse those values."))),
                DescribeRole.Theorem))));
}
