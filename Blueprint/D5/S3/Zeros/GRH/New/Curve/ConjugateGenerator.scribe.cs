using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Curve;

internal sealed class ConjugateGeneratorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugate Generator", H("Conjugate Generator"),
        Blocks(
            Paragraph(Text("Galois action on translates of a theta product; integral bounded scaled vacuum values.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Curve/ConjugateGenerator.exists_isJetConjugate_generator"),
                H("exists_isJetConjugate_generator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Some C and, for each s, adeles b_σ serve all standard V of rank n: some c ≠ 0 makes the values of c·vac integral, with K-conjugates ≤ e^{CN₁²n}; translates of some F ∈ 𝒲_f, θF = 1, span 𝒲_f; and σT_per ϱ(x)F = T_t ϱ(b_σx)F′ (places permuted), some F′ ∈ 𝒲_f, |t|² = 1/Ω. Here T_a = Space.jetSeries a, per = Parameters.jetScale, 𝒲_f = Space.finitePart.")))))));
}
