using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel;
internal sealed class ProtectedFillingsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings",
            "Path and excluded-cycle fillings.",
            "all-m-protected-source-only",
            [Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")]),
        H("Path and excluded-cycle fillings"),
        Blocks(Paragraph(Text("Maximal-critical protection constructs the path contract, the good-residue path Gamma, the zero filling on the unchanged tail ground and the excluded-residue cycle filling. The zero filling retains forbidden endpoint ghosts and the raw empty critical face in the small cases.")))));
}
