using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringWeylInqDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weyl differencing inequality",
        H("Weyl differencing inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weylinq"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringWeylInq.normSq_expSum_le"),
                H("Weyl differencing inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("Group the pairs by their signed displacement and bound the squared norm by the sum of the norms of the displacement sums. The unit-interval Fourier calculation uses the coefficient at zero of a period-one Mathlib character."))),
                DescribeRole.Theorem)
        )));
}
