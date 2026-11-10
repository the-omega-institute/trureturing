using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;
internal sealed class HistoryLocalLeavesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/HistoryLocalLeaves",
            "Original-mask local leaf constructions.",
            "original-coordinate-constructions",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("Original-mask local leaf constructions"),
        Blocks(Paragraph(Text("The original corner masks and retained ground determine the actual family decompositions. Singleton, one-leaf and two-leaf rows construct genuine Output values, while the path-component lemmas find an unmarked leaf. Ground transport preserves the original families rather than introducing a desired output as an assumption.")))));
}
