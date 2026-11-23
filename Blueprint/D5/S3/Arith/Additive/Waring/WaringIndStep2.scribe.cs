using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringIndStep2Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Induction in the polynomial degree",
        H("Induction in the polynomial degree"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("indstep2"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringIndStep2.meanValueBound_all"),
                H("Induction in the polynomial degree"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("The quadratic base case and the estimate for differenced polynomials yield the mean-value bound for every polynomial degree at least two."))),
                DescribeRole.Theorem)
        )));
}
