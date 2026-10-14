using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteCachedSymmetryDAGReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteCachedSymmetryDAGReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sound actual-context shared-DAG checking with a proved cache",
        H("Sound actual-context shared-DAG checking with a proved cache"),
        Blocks(
            Paragraph(Text("Every split checks all values with the actual updated partial assignment and new cache; bound nodes check the cache lower and symmetry nodes check actual dominance. A fuel-indexed semantic cache invariant must be proved initially and across every successful split with positive remaining child fuel. Exhausted-fuel child checks reject directly and do not require irrelevant known-coordinate transitions. No node index alone transfers arithmetic or context correctness.")),
            Node("check", "check", "Full actual-context cached Boolean replay",
                "Fuel zero returns false. Bound, symmetry and split checks retain the same complete actual event semantics and every possible value branch.", DescribeRole.Definition),
            Node("check-prefix", "checkPrefix", "Finite prefix checking retains exact suffix contexts",
                "The prefix uses the original bound and symmetry checks and every possible value branch. At its frontier it passes the exact remaining fuel, node index, full cache and partial event to a separately justified suffix selector. A shared shape or hash cannot replace that actual context.", DescribeRole.Definition),
            Node("checked-prefix-and-frontier", "checked_prefix_and_frontier", "Complete suffix receipts compose with the prefix",
                "Induction on prefix depth turns prefix acceptance into the existing complete replay acceptance when every selected exact suffix context has its own full replay receipt. Early bound and symmetry checks stay unchanged. The existing global lower-bound theorem supplies the same score and rank-descent conclusions after this composition.", DescribeRole.Theorem),
            Node("checked-forces-smaller-bad-event", "checked_forces_smaller_bad_event", "Every accepted bad event earns strict rank descent",
                "Fuel induction uses the proved cache lower invariant at bounds, actual dominance at symmetry cuts and actual compatibility/update plus cache validity at each selected complete-event branch. An exhausted child is rejected before any unnecessary step premise is used.", DescribeRole.Theorem),
            Node("checked-global-lower-bound", "checked_global_lower_bound", "Full accepted cached replay bounds every original event",
                "Strong induction on the event's natural-number rank rules out any bad event using the previous descent theorem. Exact score invariance, complete actual acceptance and all semantic cache obligations are mandatory.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
