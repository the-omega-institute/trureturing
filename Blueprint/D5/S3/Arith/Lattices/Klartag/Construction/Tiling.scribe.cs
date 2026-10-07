using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Construction;

internal sealed class TilingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Construction/Tiling.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construction A lattices, covolumes and ellipsoid transfer.",
        H("Tiling"),
        Blocks(
            Paragraph(Text("Construction A lattices, covolumes and ellipsoid transfer. The results below relate tiling to the stochastic ellipsoid construction.")),
            Node("claim-1", "toE", "to E",
                "The embedding ℤⁿ ↪ ℝⁿ (Euclidean).", DescribeRole.Definition),
            Node("claim-2", "cube", "cube",
                "The open unit cube centred at c.", DescribeRole.Definition),
            Node("claim-7", "cube_disjoint", "cube disjoint",
                "Cubes centred at distinct integer points are disjoint.", DescribeRole.Theorem),
            Node("claim-9", "card_le_volume_ball", "card le volume ball",
                "Cube packing. A finite set of integer points of norm ≤ R has cardinality at most the volume of the ball of radius R + √n/2.", DescribeRole.Theorem),
            Node("claim-10", "sum_le_lintegral", "sum le lintegral",
                "Sum-to-integral comparison (the cube-tiling lemma, in the form that needs no φ↑): a finite lattice sum is bounded by the integral of any function dominating it on each cube.", DescribeRole.Theorem),
            Node("claim-11", "abs_coord_le_norm", "abs coord le norm",
                "A coordinate is bounded by the Euclidean norm.", DescribeRole.Theorem),
            Node("claim-12", "finite_ball_integer", "finite ball integer",
                "Set finiteness. A Euclidean ball contains finitely many integer points.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
