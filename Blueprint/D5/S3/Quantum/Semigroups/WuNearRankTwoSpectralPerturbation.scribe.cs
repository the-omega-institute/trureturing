using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuNearRankTwoSpectralPerturbationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional near-rank-two spectral perturbation for the unequal-temperature cubic Gibbs deficit.",
        H("Near-rank-two spectral perturbation"),
        Blocks(
            Paragraph(Text(
                "The product Gibbs eigenvalue at occupation o is occupationWeight(r,o.1) occupationWeight(R,o.2), with occupation order 00, 01, 10, 11. "
                + "The Gibbs log field averages these four logarithms against the nonnegative frame weights p(i,o) whose sum is one.")),
            Entry("gibbs-bounds", "gibbsEigenvalue_bounds", "Product Gibbs eigenvalue bounds",
                "For R,r ≥ 1 every product Gibbs eigenvalue lies between a(r)a(R) and b(r)b(R), and the corresponding Gibbs log field lies between the logarithms of those endpoints."),
            Entry("root-raising-loss", "deficit_two_root_loss", "Two-root raising loss",
                "At the tracial spectator, replacing zero roots by values at most ε costs at most 9 ε in the deficit when ε³ ≤ 1/(2(1+R³)). The estimate includes the cubic energy loss and the entropy sign from adding mass below the least Gibbs eigenvalue."),
            Entry("temperature-transfer", "deficit_temperature_change", "Temperature variation",
                "At fixed roots and fixed frame, changing the spectator ratio from 1 to r changes the deficit by at most 26 log r. The 26 comes from the energy bound 8 log r and the entropy bound 12 log r multiplied by alpha(R) ≤ 3/4."),
            Entry("near-rank-two-lower", "near_rank_two_deficit_lower", "Combined perturbation lower bound",
                "The two-root and temperature estimates combine to deficit(R,1,...,v₀) − 9ε − 26 log r ≤ deficit(R,r,...,v)."),
            Entry("conditional-margin-transfer", "near_rank_two_unequal_temperature", "Conditional strict rank-two margin transfer",
                "For 1 < R, r ∈ [1,R], 0 ≤ u ≤ v ≤ m ≤ 1, v ≤ ε, ε ≤ min(rankTwoMargin(R)/36, (2(1+R³))^(−1/3)), and log r ≤ rankTwoMargin(R)/104, assume the strict tracial baseline hypothesis hbase: rankTwoMargin(R) · mass ![0,0,m,1] < deficit(R,1,cold,spectator,p,![0,0,m,1]). Then the actual conclusion is rankTwoMargin(R)/2 < deficit(R,r,cold,spectator,p,![u,v,m,1]). The mass factor remains in the hypothesis and is used to convert it to the strict unit-margin baseline."),
            Entry("homogeneous-restoration", "deficit_scale", "Cubic scaling restoration",
                "For h > 0, scaling every spectral root by h scales the deficit by h³, restoring arbitrary positive largest roots from the normalized theorem."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
