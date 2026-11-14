using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalComparisonTopologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original scalar-topology import compatibility", H("Original scalar-topology import compatibility"), Blocks(
            Paragraph(Text("This module imports OriginalNormalFamily. The original OriginalComparisonTopology namespace, common scalar definitions, complete common continuity-set theorem and both directions of the all-P local optimal-budget equivalence are available through that import. The whole-ball, singleton, subsequence and discontinuity scalar applications are derived inside the existing complete aggregate proof and explained in the owning OriginalNormalFamily exposition. This import module owns no mathematical declaration.")))));
}
