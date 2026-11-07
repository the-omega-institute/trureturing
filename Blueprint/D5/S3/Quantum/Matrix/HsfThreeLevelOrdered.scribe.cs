using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfThreeLevelOrderedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered matrix moment transfer",
        H("Ordered matrix moment transfer"),
        Blocks(Paragraph(Text("The coefficient Gram laws transfer entrywise to arbitrary finite fibers with complex phases. The ordered row-square identity retains both triangle orientations. The actual factorial CFC shifted identity is supplied by HsfLocalSpectrumSupplier; no scalar-matrix restriction is introduced.")))));
}
