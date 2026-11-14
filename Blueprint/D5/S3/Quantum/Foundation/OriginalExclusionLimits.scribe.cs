using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalExclusionLimitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original exclusion-limit import compatibility", H("Original exclusion-limit import compatibility"), Blocks(
            Paragraph(Text("This module imports OriginalNormalFamily. The original OriginalExclusionLimits namespace, whole-exclusion collapse, compact-diameter support, regular region and exact Hausdorff continuity statements are available through that import. Their proofs and the full Baire and diameter application exposition belong to OriginalNormalFamily. This import module owns no mathematical declaration.")))));
}
