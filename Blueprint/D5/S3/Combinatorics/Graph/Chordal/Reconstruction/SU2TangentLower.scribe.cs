using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal.Reconstruction;

internal sealed class SU2TangentLowerDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/Chordal/Reconstruction/SU2TangentLower";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Round unit-quaternion reconstruction dominates three-dimensional Euclidean reconstruction on each fixed finite connected graph.",
        Blocks(
            Result("fixed-graph-euclidean-three-transfer", "fixed_graph_euclidean_three_transfer", "Fixed-graph tangent transfer",
                "Every round unit-quaternion coefficient on a fixed finite connected graph is an admissible coefficient for three-dimensional Euclidean gains on that graph.",
                "First-order imaginary quaternion curves encode the gains. Normalize each fitted quaternion potential at one vertex and use bounded displacements along fixed finite walks. Project the rescaled ambient differences to imaginary coordinates and remove slack by closed-range minimization."),
            Result("fixed-graph-euclidean-three-scaled", "fixed_graph_euclidean_three_scaled", "Tangent transfer at all defect scales",
                "The resulting Euclidean fit has error bounded by the coefficient times any nonnegative triangle-defect budget.",
                "Scale at positive budgets and use finite-dimensional closure as the scale decreases to a zero budget."),
            Result("round-width-four-family-lower", "round_width_four_family_lower", "Width-four family lower bound",
                "A round coefficient that works on every finite width-four power path is at least the square root of three halves.",
                "Apply the fixed-graph transfer and the affine regular tetrahedron obstruction to the entire family of path lengths."),
            Result("exists-round-width-four-obstruction", "exists_round_width_four_obstruction", "Finite round obstruction",
                "Every nonnegative coefficient strictly below the square root of three halves fails on some finite width-four power path with positive defect budget.",
                "The family lower bound supplies gains and a budget for which each potential in the full unit-quaternion group has an edge residual exceeding the proposed bound."))));

    private static DocumentBlock.Describe Result(string id, string declaration, string heading,
        params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()), DescribeRole.Theorem);
}
