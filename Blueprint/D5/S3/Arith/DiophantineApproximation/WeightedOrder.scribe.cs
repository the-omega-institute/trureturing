using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class WeightedOrderDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted order is additive under multiplication over a domain.",
        H("Weighted Order"),
        Blocks(Describe.Lean(
            DescribeId.Create("weighted-order"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/WeightedOrder.weightedOrder_mul"),
            H("Weighted Order"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Weighted order is additive under multiplication over a domain."))),
            DescribeRole.Theorem))));
}
