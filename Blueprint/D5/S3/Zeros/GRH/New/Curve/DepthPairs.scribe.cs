using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Curve;

internal sealed class DepthPairsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Depth Pairs", H("Depth Pairs"),
        Blocks(
            Paragraph(Text("Choice of admissible pairs and numerical bound against the predicted valuation F(p). Pairs construction: Frobenius couplings force a large coefficient on six copies.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Curve/DepthPairs.exists_hasLargeSplit_of_pairs"),
                H("exists_hasLargeSplit_of_pairs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let (p/d) ≠ 1, Θ in Parameters.thetaProducts (δ = r = 1, one copy), Θ(0) = 1, Θ carried by one copy and Θ⁻¹ by five (IsCarriedBy), (i, y) admissible for n (IsFrobPacking). Then some b, τ ≤ n with |b| = ∑y_σ(p^{i_σ} + 1), |τ| = ∑y_σ satisfy HasLargeSplit N 6 b (p^{(1 − 1/(p−1))|τ| + ρ_p|b|}/|τ!|_p).")))))));
}
