using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class RealMatchingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real Matching", H("Real Matching"),
        Blocks(
            Paragraph(Text("Real-place matching of determinant polynomials via invariant functionals on Fock space.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/RealMatching.real_matching"),
                H("real_matching"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Archimedean step of explicit matching, weights γ_τ = |l| − |ι_τ|. For some polynomial Q₀, each v has κ such that, if ℓ_g(Ω(x)w) = ℓ_{gx₁}(w) and ℓ_x(v) = ℓ′(Q) whenever Ω(1, x)v_{Q₀} = v_Q, then κ·ℓ₁(posFockVector j (stackedDetProd e η)) = ℓ′(matchedPoly f j η) for all η.")))))));
}
