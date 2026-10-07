using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Construction;

internal sealed class LiftBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Construction/LiftBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construction A lattices, covolumes and ellipsoid transfer.",
        H("Lift Bound"),
        Blocks(
            Paragraph(Text("Construction A lattices, covolumes and ellipsoid transfer. The results below relate lift bound to the stochastic ellipsoid construction.")),
            Node("claim-1", "sum_card_newActive", "sum card new Active",
                "The freezes partition the active set. A step never breaks an already-active constraint (Chain.newActive_disjoint), so the counts add.", DescribeRole.Theorem),
            Node("claim-2", "norm_liftSum_le_card", "norm lift Sum le card",
                "The accumulated lift, with no per-step count and no dim.", DescribeRole.Theorem),
            Node("claim-3", "stateBounds_of_chain_count", "state Bounds of chain count",
                "The per-path core with the accumulated lift bound (StateInvariantGlue.stateBounds_of_chain takes the per-step one and pays a factor dim).", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
