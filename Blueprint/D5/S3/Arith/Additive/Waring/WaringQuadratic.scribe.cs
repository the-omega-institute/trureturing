using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringQuadraticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounding a quadratic moment by fibers",
        H("Bounding a quadratic moment by fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadratic"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringQuadratic.qHMCount_le_sum_sq"),
                H("Bounding a quadratic moment by fibers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("The zero-sum quadratic count is bounded by the sum of squares of the quadratic phase-fiber counts over their bounded range."))),
                DescribeRole.Theorem)
        )));
}
