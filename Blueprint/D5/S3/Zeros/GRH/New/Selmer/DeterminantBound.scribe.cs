using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class DeterminantBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Determinant Bound", H("Determinant Bound"),
        Blocks(
            Paragraph(Text("Bloch–Kato finite condition at places above ℓ as relations on global cocycles. Conditions on Hodge-Tate jumps of a row; explicit crystalline loss per prime. Dictionary between complex embeddings, places above l and cosets of local Galois groups. Operators clearing denominators at each eigenvector combine to bound the Gram determinant.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/DeterminantBound.norm_gram_det_le_of_operators"),
                H("norm_gram_det_le_of_operators"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let A span Z, of finite dimension, x_b ∈ Z. Suppose each nonzero p ∈ A has a map G, a multiple of j on each v ∈ A, whose scalars ι⁻¹(l) at p have ‖lm‖ ≥ e^{−γ}, and ‖m·ιη_a(w)‖ ≤ 1 if w ∈ Z, jw = Gx_b. Then ‖ι det η_a(x_b)‖ ≤ e^{γ dim Z}.")))))));
}
