using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalComparisonTopologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original scalar-topology import compatibility", H("Original scalar-topology import compatibility"), Blocks(
            Paragraph(Text("This module imports OriginalNormalFamily. The original OriginalComparisonTopology namespace, exact scalar branches, semicontinuity statements, common continuity sets and all-P local optimal-budget results are available through that import. Their mathematical statements and exposition belong to OriginalNormalFamily. This import module owns no mathematical declaration.")))));
}
