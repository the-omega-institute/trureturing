using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;
internal sealed class HistoryPhysicalStepsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/HistoryPhysicalSteps",
            "Physical rows and earlier-history step outputs.",
            "original-coordinate-constructions",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("Physical rows and earlier-history step outputs"),
        Blocks(Paragraph(Text("The actual wheel labels identify physical rim rows and their projected incidence. Leaf and neighbour cases are proved at those original positions. Earlier-history outputs then construct empty-row, zero-local, unused-local, marker and intact terminal steps, using the stated old-history input and the same residual masks.")))));
}
