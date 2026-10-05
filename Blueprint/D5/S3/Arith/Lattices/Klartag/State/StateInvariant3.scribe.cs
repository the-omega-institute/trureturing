using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.State;

internal sealed class StateInvariant3Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/State/StateInvariant3.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric matrix state invariants and padded driving laws.",
        H("State Invariant3"),
        Blocks(
            Paragraph(Text("Symmetric matrix state invariants and padded driving laws. The results below relate state invariant3 to the stochastic ellipsoid construction.")),
            Node("claim-1", "reflection_congr", "reflection congr",
                "Submodule.reflection carries a HasOrthogonalProjection instance argument depending on the subspace, so rw on the subspace fails (\"motive is not type correct\"). subst does not.", DescribeRole.Theorem),
            Node("claim-4", "map_sum_xi", "map sum xi",
                "(B1) Σ_{j<k} ξ_j ~ N(0, k c² · Id).", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
