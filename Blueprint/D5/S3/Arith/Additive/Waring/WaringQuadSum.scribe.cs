using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringQuadSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourth moment of the displacement sums",
        H("Fourth moment of the displacement sums"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadsum"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringQuadSum.integral_sum_pow_four"),
                H("Fourth moment of the displacement sums"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("Integration over the unit interval retains the four phase fibers whose integer phases sum to zero, weighted by the product of their cardinalities."))),
                DescribeRole.Theorem)
        )));
}
