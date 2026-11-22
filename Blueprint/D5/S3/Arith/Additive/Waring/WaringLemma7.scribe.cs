using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringLemma7Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counting four bilinear terms",
        H("Counting four bilinear terms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lemma7"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringLemma7.hmCount7_le"),
                H("Counting four bilinear terms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("For 1 ≤ H ≤ M the count of boxed solutions whose four bilinear terms sum to zero is at most 5250(HM)³."))),
                DescribeRole.Theorem)
        )));
}
