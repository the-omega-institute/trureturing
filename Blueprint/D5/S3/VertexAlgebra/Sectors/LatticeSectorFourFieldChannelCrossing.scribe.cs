using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorFourFieldChannelCrossingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite four-field channel crossing readout across FullIO reassociation",
        H("Four-field channel crossing readout"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticesectorfourfieldchannelcrossing-actual-four-field-channel-crossing"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldChannelCrossing."
                        + "actual_four_field_channel_crossing"),
                H("Actual four-field channel crossing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem keeps one cleared four-field numerator and transports the "
                        + "finite middle-channel readout through the explicit FullIO charge "
                        + "reassociation. It identifies the middle and short channel readouts "
                        + "at the same finite coefficient, without asserting analytic sewing, "
                        + "a full pentagon, or an infinite summation."))),
                DescribeRole.Theorem))));
}
