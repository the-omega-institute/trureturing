using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift.Stopped;

internal sealed class DriftStopped8Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stopped log determinant drift and integrability estimates.",
        H("Drift Stopped8"),
        Blocks(
            Paragraph(Text("Stopped log determinant drift and integrability estimates. The results below relate drift stopped8 to the stochastic ellipsoid construction.")),
            Node("claim-1", "quad_eq_inner", "quad eq inner",
                "The ellipsoid's quadratic form as an inner product, so StateBounds.lower applies to it.", DescribeRole.Theorem),
            Node("claim-2", "norm_lt_reach", "norm lt reach",
                "The reach. StateBounds A m M bounds the ellipsoid inside the ball of radius 1/√m: m‖v‖² ≤ ⟪v, Av⟫ < 1.", DescribeRole.Theorem),
            Node("claim-3", "notMem_ellipsoid_of_reach", "not Mem ellipsoid of reach",
                "A lattice point at or beyond the reach is outside the ellipsoid, with no counting at all.", DescribeRole.Theorem),
            Node("claim-6", "notMem_ellipsoid_of_mem_kSet", "not Mem ellipsoid of mem k Set",
                "The shell case, and it needs no probabilistic input. Chain.kSet is the set of matrices whose ellipsoid misses the window, and Chain.chain_fst_mem_kSet keeps the chain inside it at every step and on every path.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
