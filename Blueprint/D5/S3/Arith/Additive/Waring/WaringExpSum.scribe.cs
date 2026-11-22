using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringExpSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Squared norm of an exponential sum",
        H("Squared norm of an exponential sum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("expsum"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringExpSum.normSq_expSum"),
                H("Squared norm of an exponential sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("The squared norm expands as the double sum over all pairs of input indices, with phase given by the difference of their images."))),
                DescribeRole.Theorem)
        )));
}
