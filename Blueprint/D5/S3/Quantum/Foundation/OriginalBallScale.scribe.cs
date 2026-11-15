using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalBallScaleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original scale import compatibility",
        H("Original scale import compatibility"), Blocks(
            Paragraph(Text("This module imports OriginalNormalFamily. The original OriginalBallScale namespace, statements, positive-extension budgets and mixed-input comparison laws are available through that import. Their mathematical declarations and theorem exposition belong to OriginalNormalFamily, together with the original whole-cone normal-positivity construction. This import module owns no mathematical declaration.")))));
}
