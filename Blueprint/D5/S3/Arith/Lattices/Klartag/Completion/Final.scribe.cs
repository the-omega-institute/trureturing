using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class FinalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/Final.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Final"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate final to the stochastic ellipsoid construction.")),
            Node("claim-1", "abs_coord_le_norm", "abs coord le norm",
                "Every coordinate of a Euclidean vector is bounded by its norm.", DescribeRole.Theorem),
            Node("claim-2", "integerPoints_ball", "integer Points ball",
                "The unit ball has no non-zero integer point — the open cube (−1,1)^N contains it, and an integer of absolute value < 1 is 0.", DescribeRole.Theorem),
            Node("claim-3", "ballVol", "ball Vol",
                "Vol(B^N) as a real number.", DescribeRole.Definition),
            Node("claim-6", "smallConst", "small Const",
                "c₁ = min_{1 ≤ m < n₁} Vol(B^{m+1}) / m², a minimum over a finite set.", DescribeRole.Definition),
            Node("claim-9", "small_volume_ge", "small volume ge",
                "The small-dimension bound in the form klartag_of_volume_ge consumes.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
