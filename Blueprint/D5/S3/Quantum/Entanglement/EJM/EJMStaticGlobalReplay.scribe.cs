using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMStaticGlobalReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMStaticGlobalReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direct leaf association for the original EJM score",
        H("Direct leaf association for the original EJM score"),
        Blocks(
            Paragraph(Text("This is a conditional soundness bridge for a static annotated certificate. It preserves the original F1, F2, 6987435 threshold, original 16 triangle and 16 singleton projections, and global score-preserving symmetries. The executable checker differs from recursive original-DAG replay: it checks explicit actual partial contexts, complete successor coverage and direct leaf snapshots. No complete global table, Boolean acceptance or unconditional locality refutation is supplied by this bridge.")),
            Node("triangle-snapshot", "checkTriangleSnapshot", "Check the exact triangle row and action association",
                "The proposed row's hash, scaled lower value, slots and edges equal the original mirror row selected by its exact row index. Its full local assignment equals the exact coordinate and outcome action applied to the original projected partial assignment.", DescribeRole.Definition),
            Node("singleton-snapshot", "checkSingletonSnapshot", "Check the exact singleton row and action association",
                "The same complete checks use the original singleton row family and action. A producer hash, shared rule number or a lower value alone supplies no acceptance.", DescribeRole.Definition),
            Node("bound-snapshot", "checkBoundSnapshot", "Check all original local projections and the original threshold",
                "All 16 triangle and all 16 singleton projections must pass their own exact association checks. The sum of their same original scaled lower values must reach 6987435.", DescribeRole.Definition),
            Node("bound-soundness", "checked_bound_snapshot", "An accepted snapshot bounds every compatible original event",
                "Complete mirror and assignment receipts reconstruct AssociatedCache. The established associated_lower_le_score theorem then bounds the original EJM score without replaying every ancestral cache transition at this leaf.", DescribeRole.Theorem),
            Node("global-bound", "accepted_score_lower_bound", "A fully checked static certificate proves the original score margin",
                "Every annotated row must pass the checker, and the designated root must carry the all-unknown assignment. The generic row-level and event-rank descent theorem then proves score F1 F2 e at least 6987435 for every original event. This conclusion is conditional until the complete actual table and its acceptance are earned.", DescribeRole.Theorem),
            Node("locality", "accepted_excludes_triangle_local", "Complete static acceptance excludes triangle locality",
                "The same complete-acceptance hypotheses yield a positive original inflation score, which the existing faithful triangle-local refutation theorem consumes. This is not an unconditional nonlocality result or a completed acceptance certificate.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
