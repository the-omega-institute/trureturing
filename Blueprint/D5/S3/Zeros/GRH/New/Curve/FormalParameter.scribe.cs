using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Curve;

internal sealed class FormalParameterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Formal Parameter", H("Formal Parameter"),
        Blocks(
            Paragraph(Text("Jets of products of torsion translates of theta are integral after scaling. Valuations of coefficients of log theta: only two degrees keep a denominator. Property: series integral on substitutions killing the Frobenius couplings. Good formal parameter and three-term normal form of log theta at non-split primes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Curve/FormalParameter.exists_formal_parameter"),
                H("exists_formal_parameter"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let p ≥ 13 if (p/d) ≠ 1. Some T ∈ 𝔬[[φ]], |ϖ| = p^{−ρ_p}, q = p^e > 1, 1/p ≤ |π| < 1 have T(ϖX) = ϖS, S integral, S(0) = 0, S − S^q ≡ X mod π. If (p/d) ≠ 1, some integral ψ ≡ u₀X² + u₁S^{p+1} + u₂S^{p+q} mod π (u₀ = 0, u₁ a unit unless p = d = q) gives, for n prime to p, a unit N and κ, |κ| = p^{(1−(p/d))/2−1/(p−1)}, with (U_yθ)(ϖX) ∈ (exp(κψ)𝔬[[X]])(NX) whenever ny ∈ Λ.")))))));
}
