using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringLinnikDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "From positive density to a Waring bound",
        H("From positive density to a Waring bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("linnik"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringLinnik.isWaringBound_of_positive_density"),
                H("From positive density to a Waring bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("If numbers represented by at most s nonnegative kth powers have a positive lower density, their finite additive-basis order gives a uniform bound on the number of kth powers needed."))),
                DescribeRole.Theorem)
        )));
}
