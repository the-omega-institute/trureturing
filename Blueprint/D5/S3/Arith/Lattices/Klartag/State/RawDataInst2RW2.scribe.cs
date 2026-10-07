using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.State;

internal sealed class RawDataInst2RW2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/State/RawDataInst2RW2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric matrix state invariants and padded driving laws.",
        H("Raw Data Inst2RW2"),
        Blocks(
            Paragraph(Text("Symmetric matrix state invariants and padded driving laws. The results below relate raw data inst2rw2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "shellR", "shell R",
                "The chain's window at the reach: the integer points between (1−1/n)/α (exclusive) and windowR2 α n − √n/2 (inclusive).", DescribeRole.Definition),
            Node("claim-3", "inner_radiusR", "inner radius R",
                "The inner radius, unscaled, on the reach shell.", DescribeRole.Theorem),
            Node("claim-4", "a0C_mul_sq_gt_one_of_inner", "a0C mul sq gt one of inner",
                "a₀·(α‖toE y‖)² > 1 from the inner radius alone — the window plays no part, so this serves both lanes.", DescribeRole.Theorem),
            Node("claim-5", "lattice_fieldsR", "lattice fields R",
                "The seven lattice fields, for the chain's own q, A₀ and the reach shell.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
