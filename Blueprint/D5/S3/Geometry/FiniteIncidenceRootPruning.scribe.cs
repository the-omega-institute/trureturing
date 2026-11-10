using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;
internal sealed class FiniteIncidenceRootPruningDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/FiniteIncidenceRootPruning",
            "Original-ground incidence pruning.",
            "original-coordinate-constructions",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("Original-ground incidence pruning"),
        Blocks(Paragraph(Text("Finite incidence states retain their independent row and column types. The literal root complex, pruning constructors, terminal alternatives and collapse witnesses retain empty rows, original active labels and critical supports. Simplex, isolated-column and singleton-row constructions supply the recursive consumer.")))));
}
