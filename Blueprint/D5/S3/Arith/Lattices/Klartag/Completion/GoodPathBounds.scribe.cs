using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class GoodPathBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Good Path Bounds"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate good path bounds to the stochastic ellipsoid construction.")),
            Node("claim-2", "hS_of_intWeight", "h S of int Weight",
                "hS, derived. GoodPathLight.sum_free_ge_cut at Nfun := stoppedFreeDim, Cset := C_k, Good k := {k < τ}, dd := dim E, with the contact total rewritten by ContactIntegrated.integrated_count_eq into (1/h)·∑_{W} intWeight and bounded by the light contact.", DescribeRole.Theorem),
            Node("claim-6", "stateGood_of_goodCut", "state Good of good Cut",
                "On goodCut the state conditions hold at every index up to K.", DescribeRole.Theorem),
            Node("claim-7", "lt_tau_of_goodCut", "lt tau of good Cut",
                "Hence the stopping time has not fired by K.", DescribeRole.Theorem),
            Node("claim-8", "stateBounds_goodCut", "state Bounds good Cut",
                "StateBounds at index K on goodCut — StateInvariant4.stateBounds_wired''s proof with the count taken at K directly instead of transported from N.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
