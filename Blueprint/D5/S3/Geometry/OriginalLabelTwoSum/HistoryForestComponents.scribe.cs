using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;
internal sealed class HistoryForestComponentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/HistoryForestComponents",
            "Original-label path components.",
            "original-coordinate-constructions",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("Original-label path components"),
        Blocks(Paragraph(Text("Rows keep their actual indices and multiplicities. Singleton constraints force original labels, while pruning removes only redundant size-two rows touching those forced labels. Connectivity is characterized by surviving consecutive cut intervals; component roots, singleton ghosts and untouched endpoint connectivity use the same original path positions.")))));
}
