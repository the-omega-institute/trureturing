using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringWeylDiffDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial finite differences",
        H("Polynomial finite differences"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weyldiff"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringWeylDiff.diffH_polyEval"),
                H("Polynomial finite differences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("The step-h difference of an integer polynomial is h times the polynomial with the divided difference coefficients."))),
                DescribeRole.Theorem)
        )));
}
