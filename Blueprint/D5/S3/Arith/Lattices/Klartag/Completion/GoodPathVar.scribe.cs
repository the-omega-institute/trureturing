using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class GoodPathVarDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/GoodPathVar.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Good Path Var"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate good path var to the stochastic ellipsoid construction.")),
            Node("claim-1", "pos_part_split", "pos part split",
                "(x − L)⁺ = (x − L) + (L − x)⁺.", DescribeRole.Theorem),
            Node("claim-4", "exists_mem_of_variance", "exists mem of variance",
                "The existence step against a lower-tail bound. s is the expected shortfall below L and f the good event's failure probability. Markov runs on (X − L)⁺, so nothing here needs a pointwise floor for X — which is the whole point: the floor n·log (mAt n c₃) is what made GoodPathBounds.exists_mem_of_integral_le's margin decay like 1/n.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
