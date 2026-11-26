using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Endgame;

internal sealed class LongFormsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Long Forms", H("Long Forms"),
        Blocks(
            Paragraph(Text("Theorem C (Data.integral_forms_long: a lower bound for the covolume of the lifts of an almost spanning family of small index), and the family given by Theorems A and B.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Endgame/LongForms.exists_family_covolumeSq_le"),
                H("exists_family_covolumeSq_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("There are n ≥ (1 − 4/b²)D independent rows, D = dim(rows), of index at most 5D log(1 + b²) fa log³ b, whose untwisted lifts have squared covolume at most exp(n(h_main − m·rem + fa log⁴ b)) at all σ ∈ Aut ℂ.")))))));
}
