using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Patching;

internal sealed class OnePrimeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One Prime", H("One Prime"),
        Blocks(
            Paragraph(Text("Transfer to finite GL_n of a line-stabiliser character factors through the determinant. First-order deformation of the trace at one prime via logarithm and transfer, abstract ring form.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Patching/OnePrime.one_prime_first_order"),
                H("one_prime_first_order"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let σ kill m, N = ∑ρ(g), |Γ| regular, ρ(H) fix B1, LB1 = 0, Lρ(g) = L, ∑_H ρ(p⁻¹)Ψρ(p) = n, k·transfer(a)(γ) = k, B shift by a under H, 𝒜 contain ρ(Γ), im B and commute with ac. Then some F ∈ 𝒜 has σ(nF(ρ(g) − 1)) = σ(NZ_g), LZ_g = 0, and 2kσ(F·ac t) = 2kσ(Nr) under two weighted-sum identities linking t, t', r.")))))));
}
