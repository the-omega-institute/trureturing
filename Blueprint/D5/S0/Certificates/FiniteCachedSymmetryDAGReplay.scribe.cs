using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteCachedSymmetryDAGReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteCachedSymmetryDAGReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact context replay with finite cached updates",
        H("Exact context replay with finite cached updates"),
        Blocks(
            Paragraph(Text("Each actual occurrence retains its own full cache and partial assignment. The global theorem uses proved cache validity and a strict rank decrease at symmetry leaves. Complete replay acceptance remains an explicit premise.")),
            Node("check", "check", "Replay every actual value branch",
                "Fuel zero rejects. Bound leaves check the current lower, symmetry leaves check actual-context domination, and splits update the cache and partial assignment for every finite value.", DescribeRole.Definition),
            Node("checked-split", "checked_split", "Assemble all actual child contexts",
                "An exact literal split-node equality and acceptance of every actual child with its actual updated cache and partial assignment imply acceptance of the parent.", DescribeRole.Theorem),
            Node("checkSplit", "checkSplit", "Check a complete literal split proposal",
                "The actual node must be a split. Its coordinate and all finite value children must equal the proposal; no symmetry-type equality or context-free acceptance is used.", DescribeRole.Definition),
            Node("checked-split-node", "checked_split_node", "Recover the full split-node equality",
                "A successful finite split-proposal check proves equality of both the coordinate and the whole child function.", DescribeRole.Theorem),
            Node("checkPrefix", "checkPrefix", "Pass the full actual context at a frontier",
                "A fixed prefix retains the original bound and symmetry tests. Its frontier receives remaining fuel, node index, full cache and full partial assignment.", DescribeRole.Definition),
            Node("checked-prefix-and-frontier", "checked_prefix_and_frontier", "Splice separately checked suffixes",
                "Every frontier acceptance must imply the corresponding exact full check. Induction through all prefix branches recovers the original full replay.", DescribeRole.Theorem),
            Node("checked-forces-smaller-bad-event", "checked_forces_smaller_bad_event", "An accepted replay decreases every bad event",
                "The actual cache invariant supplies bound soundness; an exhaustive actual split follows the compatible event; an accepted symmetry cut gives a strictly smaller bad event.", DescribeRole.Theorem),
            Node("checked-global-lower-bound", "checked_global_lower_bound", "Complete actual acceptance forces the global bound",
                "Strong induction on the complete-event natural rank excludes every event below the gap. All concrete lower, update, score-invariance and domination obligations remain explicit.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
