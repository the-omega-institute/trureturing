using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class StableCellsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stable Cells", H("Stable Cells"),
        Blocks(
            Paragraph(Text("Invariance of link, level and discriminant under unipotent groups; link is Lagrangian (link: classes of the pairs (y, γ⁻¹y), y orthogonal to X and γX, X spanned by e₁, …, e_ϱ).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/StableCells.link_big_cell_eq_iff"),
                H("link_big_cell_eq_iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Over a field with involution, let σ, τ fix all e_a, e*_a, and let w_p, w_q be Weyl elements of length ϱ. Then w_pσ and w_qτ have the same link if and only if σ = τ.")))))));
}
