using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringHolderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A power-sum inequality",
        H("A power-sum inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("holder"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringHolder.sum_pow_le_card_pow_mul_sum_pow"),
                H("A power-sum inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("For nonnegative entries on a finite set and a positive integer exponent m, the mth power of their sum is bounded by the sum of their mth powers times the cardinality to the power m−1."))),
                DescribeRole.Theorem)
        )));
}
