using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringLemma8FormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic fiber second moment",
        H("Quadratic fiber second moment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lemma8form"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringLemma8Form.sum_qQ_sq_le_K"),
                H("Quadratic fiber second moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("For a nonzero quadratic coefficient and N ≥ 1, the sum of squared phase-fiber counts is at most 10000 times the phase-range bound times N⁴."))),
                DescribeRole.Theorem)
        )));
}
