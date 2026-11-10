using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel;
internal sealed class CycleWordConstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWordConstruction",
            "Original-coordinate constructions used by the paired mathematical consumer.",
            "original-coordinate-constructions",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("Original-coordinate constructions"),
        Blocks(Paragraph(Text("The declarations retain their original namespaces, hypotheses and proof bodies. Their mathematical descriptions and precise public handles are in the D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord document; this module supplies the construction dependency used by that consumer.")))));
}
