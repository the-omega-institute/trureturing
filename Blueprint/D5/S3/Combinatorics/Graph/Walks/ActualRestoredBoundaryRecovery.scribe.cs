using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualRestoredBoundaryRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualRestoredBoundaryRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recover Whole Actual Boundary Pieces from Retained Routes.",
        H("Recover Whole Actual Boundary Pieces from Retained Routes"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-restored-boundary-recovery-actual-missing-cycle-edge-forces-path-endpoint"), DeclarationHandle.Create(Prefix + "actual_missing_cycle_edge_forces_path_endpoint"),
                H("A Missing Cycle Edge Forces a Path Endpoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A simple path using only edges of a supplied Hamilton cycle cannot pass internally through an endpoint of an actual omitted cycle edge. Two internal neighbours would already exhaust that source-cycle vertex degree."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-restored-boundary-recovery-actual-restored-joint-route-recovers-whole-piece"), DeclarationHandle.Create(Prefix + "actual_restored_joint_route_recovers_whole_piece"),
                H("Recover the Exact Whole Restored Piece"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A retained simple route starts at an actual restored piece start and ends at a distinct vertex incident to a still-deleted actual cycle edge. Exact partition ownership first places the route inside that same piece, then the degree argument earns its other endpoint and exact full support and edge recovery."))), DescribeRole.Theorem))));
}
