// Apache-2.0.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction;

internal sealed class PureCubicFixedRankDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/PureCubicFixedRank.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three commuting cubic twists have fixed ranks summing to the ambient dimension when the twisting operator has zero cyclic norm.",
        H("Fixed Ranks in a Cubic Coset"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-rank-sum-of-commuting-cubics"),
                DeclarationHandle.Create(Prefix + "fixed_rank_sum_of_commuting_cubics"),
                H("Sum of the three fixed ranks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let V be finite-dimensional over a field of characteristic zero. Let A and C be commuting "
                        + "endomorphisms of V with A^3=C^3=I and I+C+C^2=0. The sum of the fixed-space dimensions of "
                        + "A, AC, and AC^2 equals the dimension of V.")),
                    Paragraph(Text("For each T among A, AC, and AC^2, its cube is I, so (I+T+T^2)/3 is the average onto "
                        + "its fixed space. The sum of these averages is I. The linear terms sum to A(I+C+C^2), and the "
                        + "quadratic terms sum to A^2(I+C^2+C^4). Both sums vanish since C^4=C. The trace formula for "
                        + "the order-three action gives the rank of each fixed space from the trace of its average."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pure-cubic-fixed-ranks-eq-sixteen"),
                DeclarationHandle.Create(Prefix + "pure_cubic_fixed_ranks_eq_sixteen"),
                H("Fixed rank sixteen in dimension forty-eight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the same assumptions, suppose V has dimension 48 and the fixed ranks of A, AC, "
                        + "and AC^2 each belong to the set {0,16}. Their sum is 48, so all three ranks are 16.")),
                    Paragraph(Text("In the application to P48p, A represents a cubic from the SL2(23) factor and C a "
                        + "generator of the commuting C3 factor. Nebe, arXiv:1212.0865, Theorem 3.6, proof (B), "
                        + "describes these factors, and Proposition 4.8 supplies the allowed ranks for order-three "
                        + "lattice isometries. The operator relations and allowed ranks are premises of the rank calculation."))),
                DescribeRole.Theorem))));
}
