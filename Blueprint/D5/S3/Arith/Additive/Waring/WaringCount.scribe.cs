using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A first-moment divisor estimate",
        H("A first-moment divisor estimate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("count"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringCount.sum_sigmaMinusOne_le"),
                H("A first-moment divisor estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("The sum of the reciprocals of all positive divisors, over all integers from 1 through x, is at most 2x."))),
                DescribeRole.Theorem)
        )));
}
