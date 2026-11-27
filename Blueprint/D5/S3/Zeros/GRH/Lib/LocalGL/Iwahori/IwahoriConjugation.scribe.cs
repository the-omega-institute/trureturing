using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Iwahori;

internal sealed class IwahoriConjugationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Iwahori Conjugation", H("Iwahori Conjugation"),
        Blocks(
            Paragraph(Text("Elements of I t I, t strictly dominant, are twisted-conjugate into the torus.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Iwahori/IwahoriConjugation.exists_twisted_conj_diag"),
                H("exists_twisted_conj_diag"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let σ be a continuous isometric endomorphism of the local field F, surjective on GL_n(F), and t diagonal with strictly increasing absolute values. Every g in I₁tI₁ (I₁ the pro-p Iwahori subgroup) satisfies k⁻¹gσ(k) = td with k, d in I₁, d diagonal.")))))));
}
