using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringLemma6Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A second-moment divisor estimate",
        H("A second-moment divisor estimate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lemma6"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringLemma6.sum_sigmaMinusOne_sq_le"),
                H("A second-moment divisor estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("The sum of the squares of the reciprocal-divisor statistic over 1 through x is at most 6x."))),
                DescribeRole.Theorem)
        )));
}
