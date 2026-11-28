using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.SiegelWeil.RallisInner;

internal sealed class SharpDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp Data", H("Sharp Data"),
        Blocks(
            Paragraph(Text("Doubling: inner product of theta lifts as integral of matrix coefficients; dual datum. Reversing a pair: kernel equals reversed kernel with finite Fourier transformed datum. Lifts and descents between discrete series types for families of characters; other polynomials scale. Rank-one unramified doubling sum as Euler factor; sharpness of level data.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/SiegelWeil/RallisInner/SharpData.exists_hasSum_vacuumCoeff_at_place"),
                H("exists_hasSum_vacuumCoeff_at_place"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let ν have trivial tame part at w, w̄, and k > 1. Over some representatives, supported at w, w̄, of U(1)(𝔸_f) modulo elements integral at w, vacuumCoeff(2k, νυ^k) sums to ∏_{u∈{w,w̄}} (1 − ε_u q_u^{−k})/(1 − ν̃(ϖ_u)⁻¹q_u^{−k}), ε = realZetaCoeff, ν̃ = AutChar.baseChange ν.")))))));
}
