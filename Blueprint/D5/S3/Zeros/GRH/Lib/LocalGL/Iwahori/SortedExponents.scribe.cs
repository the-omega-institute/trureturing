using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Iwahori;

internal sealed class SortedExponentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sorted Exponents", H("Sorted Exponents"),
        Blocks(
            Paragraph(Text("Exchanging and sorting the θ_i(ϖ) of exponents (torusChar θ, l); eigenvectors give exponents in unitary representations.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Iwahori/SortedExponents.exists_sorted_of_type"),
                H("exists_sorted_of_type"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let ρ be unitary, x ≠ 0 and τ as in IsExponent.exists_sorted, V_x the span of the translates of x, with finite-dimensional I₁-fixed part. Some exponent (θ, l) has l(x) ≠ 0 and θ_i = τ_i on units, and V_x holds an eigenvector for θ∘σ with |θ_{σ(i)}(ϖ)| non-increasing.")))))));
}
