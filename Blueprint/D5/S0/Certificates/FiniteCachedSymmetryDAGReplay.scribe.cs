using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteCachedSymmetryDAGReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteCachedSymmetryDAGReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exhaustive cached replay retains every actual context.",
        H("Exhaustive cached replay retains every actual context."),
        Blocks(
            Paragraph(Text("The same shared node index is evaluated with the complete actual partial assignment and its own cache. Every split checks every possible value. Bound leaves require a proved cache lower bound; symmetry leaves require an earned strict rank descent. A fuel-indexed invariant supplies only the positive-fuel transition obligations that an accepted replay can actually consume. Neither a producer assertion nor a node-only table is an acceptance premise. The complete concrete EJM consumer must establish all invariants and kernel-check the actual root replay.")),
            Describe.Lean(DescribeId.Create("check"),
                DeclarationHandle.Create(Prefix + "check"),
                H("Replay all original value branches with actual state"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Zero fuel rejects. A bound checks the cache lower, a symmetry checks dominance on the same actual partial assignment, and every split updates both that assignment and its own cache."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("checked-forces-smaller-bad-event"),
                DeclarationHandle.Create(Prefix + "checked_forces_smaller_bad_event"),
                H("Every bad original event yields a smaller bad event"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Accepted replay and the actual cache invariant force either a contradiction at a bound or an earned strict descent. The split induction consumes a validity-preserving step only when its remaining fuel is positive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("checked-global-lower-bound"),
                DeclarationHandle.Create(Prefix + "checked_global_lower_bound"),
                H("Complete acceptance proves the global lower bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Strong induction on the original event rank closes all possible bad events after full root acceptance and the initial actual-context invariant are proved. This theorem alone does not assert any concrete numerical certificate is accepted."))), DescribeRole.Theorem)))));
}
