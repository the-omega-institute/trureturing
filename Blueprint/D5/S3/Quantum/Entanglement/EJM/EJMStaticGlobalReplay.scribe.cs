using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMStaticGlobalReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMStaticGlobalReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direct leaf association for the original EJM score",
        H("Direct leaf association for the original EJM score"),
        Blocks(
            Paragraph(Text("This is a conditional soundness bridge for a static annotated certificate. It preserves the original F1, F2, 6987435 threshold, original 16 triangle and 16 singleton projections, and global score-preserving symmetries. Every shared local readout is independently checked against its original canonical row, complete transported assignment and lower value. Every actual bound leaf checks all 32 projected assignments and their original lower-value sum. Explicit actual partial contexts, complete successor coverage and event-rank descent then connect these local facts to the original global score. No complete global table, Boolean acceptance or unconditional locality refutation is supplied by this bridge.")),
            Node("global-bound", "accepted_score_lower_bound", "A fully checked static certificate proves the original score margin",
                "Every shared triangle and singleton readout must pass its original row and action checks. Each bound row independently checks all original local projections and the 6987435 sum. Every annotated row must pass the checker, and the designated root must carry the all-unknown assignment. The generic row-level and event-rank descent theorem then proves score F1 F2 e at least 6987435 for every original event. This conclusion is conditional until the complete actual table and its acceptance are earned.", DescribeRole.Theorem),
            Node("locality", "accepted_excludes_triangle_local", "Complete static acceptance excludes triangle locality",
                "The same complete-acceptance hypotheses yield a positive original inflation score, which the existing faithful triangle-local refutation theorem consumes. This is not an unconditional nonlocality result or a completed acceptance certificate.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
