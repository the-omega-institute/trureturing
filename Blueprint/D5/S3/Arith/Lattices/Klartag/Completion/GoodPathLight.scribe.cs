using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class GoodPathLightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/GoodPathLight.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Good Path Light"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate good path light to the stochastic ellipsoid construction.")),
            Node("claim-1", "sum_free_ge_cut", "sum free ge cut",
                "sum_free_ge, corrected for a cut free dimension. sum_free_ge needs dim − |C_k| ≤ Nfun k ω everywhere; when Nfun is cut at a stopping time that fails after it, and the repair is the extra term dim·∑_k P(bad k). Everything else is sum_free_ge's own argument.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
