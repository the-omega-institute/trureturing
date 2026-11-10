using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel;
internal sealed class CycleWordConstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWordConstruction",
            "Occurrence and attachment Word constructors.",
            "original-coordinate-constructions",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("Occurrence and attachment Word constructors"),
        Blocks(Paragraph(Text("The original finite grounds carry the same Symbol and Word structures. Occurrence splitting, dependency order, paired-cone words and attachment words construct actual lists with their partition, coverage and pair-dependency proofs; no path critical face is replaced by its ground complement here.")))));
}
