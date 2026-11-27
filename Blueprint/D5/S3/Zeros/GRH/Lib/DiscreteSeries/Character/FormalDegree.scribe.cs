using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Character;

internal sealed class FormalDegreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Formal Degree", H("Formal Degree"),
        Blocks(
            Paragraph(Text("Orbital integral times denominators is an antisymmetric Laurent polynomial confined by K-types. Orbital integral is Weyl's character minus off-orbit part, which lacks low monomials. Formal degree equals Weyl's dimension polynomial, and (−1)^{pq} times the sum over permutations of elliptic orbital integrals equals p!q! times the conjugate of Weyl's character.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/FormalDegree.harish_chandra_degree_and_orbital"),
                H("harish_chandra_degree_and_orbital"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Harish-Chandra: for λ of gap 500n³+10n⁵ and signature (p,q), deg_λ = ∏_{λ_j<λ_i}(λ_i−λ_j)/∏_{i<n} i!; for x in the torus with distinct entries, (−1)^{pq} Σ_{σ∈S_n} ∫_G e_λ(g⁻¹(x∘σ)g) dg = p!q!·conj χ(x), χ the character of U(n) of highest weight λ−ρ.")))))));
}
