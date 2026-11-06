using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows;

internal sealed class BasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common definitions and floor bound for the exact exceptional19 physical count.",
        H("Common definitions and floor bound"),
        Blocks(Paragraph(Text("The private definitions retain the exact five rational floors and integer normalization. The consumed rowValue_normalized and floor_on_cell lemmas provide the common positive-denominator and endpoint argument for all nineteen row modules."))), []));
}
