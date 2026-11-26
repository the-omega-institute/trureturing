using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class TwistTheoremDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twist Theorem", H("Twist Theorem"),
        Blocks(
            Paragraph(Text("Boundedly many tied primes shorten Selmer groups; one anticyclotomic twist then does, controlling L-values.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/TwistTheorem.exists_anticyclotomic_twist"),
                H("exists_anticyclotomic_twist"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let ρ_i be balanced up to β_i, val_k families, z inertial at S₀ off ℓ, v(μ(z) − 1) ≤ c, β_i + v det(ρ_i z − 1) + v det(ρ_i z^{−c} − 1) ≤ B_i < ∞, η > 0. Some I, ψ make ψ^d, 1 ≤ d ≤ m, twists (IsAuxTwist) raising v(val_k) by ≤ 8c + η, with ψ^dρ_i of Selmer length ≤ B_i + η.")))))));
}
