using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringIndStep2CountingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic mean-value base case",
        H("Quadratic mean-value base case"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("indstep2counting"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringIndStep2Counting.meanValueBoundS_two"),
                H("Quadratic mean-value base case"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("The quadratic estimate starts the mean-value induction. For arbitrary box bounds, sign compression places each fiber into the unsigned box times the four-coordinate sign box."))),
                DescribeRole.Theorem)
        )));
}
