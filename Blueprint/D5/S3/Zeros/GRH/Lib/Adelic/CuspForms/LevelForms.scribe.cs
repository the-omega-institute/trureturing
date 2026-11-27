using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.CuspForms;

internal sealed class LevelFormsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Level Forms", H("Level Forms"),
        Blocks(
            Paragraph(Text("Algebraic modular forms on definite unitary groups: inner product, conjugate norms, integral lattice.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/LevelForms.covolumeSq_elim_le"),
                H("covolumeSq_elim_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Adjoining k forms of squared norm at most e^β at σ to a family of squared covolume at most e^V gives squared covolume at most e^(V + kβ).")))))));
}
