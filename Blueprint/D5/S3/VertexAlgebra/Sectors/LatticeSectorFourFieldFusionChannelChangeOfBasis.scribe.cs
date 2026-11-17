using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorFourFieldFusionChannelChangeOfBasisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite coefficient change between the two actual four-field channels",
        H("Four-field fusion channel change of basis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticesectorfourfieldfusionchannelchangeofbasis-actual-four-field-fusion-channel-change-of-basis"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldFusionChannelChangeOfBasis."
                        + "actual_four_field_fusion_channel_change_of_basis"),
                H("Actual four-field fusion channel change of basis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem keeps one actual cleared numerator for the product and iterate "
                        + "channels, exposes the finite middle-fiber readout, and gives the explicit "
                        + "finite collision_coeff coefficient map. The charge reassociation is "
                        + "transported through the existing FullIO equivalences and the short and "
                        + "alternate four-field paths are equal. This is a bounded coefficient "
                        + "identity; it does not assert an independent fusion basis, analytic sewing, "
                        + "unitarity, a full pentagon, or an infinite summation."))),
                DescribeRole.Theorem))));
}
