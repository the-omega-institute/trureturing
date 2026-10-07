using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class StoppedLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/StoppedLowerBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Stopped Lower Bound"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate stopped lower bound to the stochastic ellipsoid construction.")),
            Node("claim-1", "stateBounds_of_stateGood", "state Bounds of state Good",
                "The state bounds from stateGood at the same index. CutSideConditions' proof with the goodCut membership replaced by the weaker stateGood, which the stopping time supplies.", DescribeRole.Theorem),
            Node("claim-2", "norm_incr_le_of_stateGood", "norm incr le of state Good",
                "The increment ceiling from stateGood one index later. stateGood (j+1) carries both ‖ξ_j‖ ≤ η and card C_{j+1} ≤ c₃, and newActive_j ⊆ C_{j+1}.", DescribeRole.Theorem),
            Node("claim-3", "logDet_stopped_ge", "log Det stopped ge",
                "The pathwise lower bound on the stopped log-determinant, at every ω. The index is K' = min K (τ−1), which is what stoppedState reads, and every j < K' is strictly below τ, so StoppedChain.stateGood_of_lt_tau discharges both side conditions with no good event.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
