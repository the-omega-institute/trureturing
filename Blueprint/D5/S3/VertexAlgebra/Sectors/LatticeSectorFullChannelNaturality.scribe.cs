using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorFullChannelNaturalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Naturality of the actual FullIO channel transport for finite target-module morphisms",
        H("FullIO channel naturality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticesectorfullchannelnaturality-full-channel-natural"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/Sectors/LatticeSectorFullChannelNaturality."
                        + "fullChannel_natural"),
                H("FullIO channel naturality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite target-module morphism g : Hom D M N, the actual "
                        + "FullIO channel transport commutes with postcomposition by g. The "
                        + "proof unfolds the channel through the incoming universal equivalence, "
                        + "uses its existing naturality, and applies the concrete incoming "
                        + "reassociation map. This is a finite algebraic naturality statement; "
                        + "it does not assert analytic sewing, convergence, a full pentagon, or "
                        + "a physical realization."))),
                DescribeRole.Theorem))));
}
