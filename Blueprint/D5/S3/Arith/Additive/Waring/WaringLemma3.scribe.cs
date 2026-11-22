using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringLemma3Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonzero bilinear fibers",
        H("Nonzero bilinear fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lemma3"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringLemma3.Q_le_sigma"),
                H("Nonzero bilinear fibers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("The count in a box for a nonzero bilinear target n is bounded by a size term and a term involving the reciprocals of the nontrivial divisors of |n|."))),
                DescribeRole.Theorem)
        )));
}
