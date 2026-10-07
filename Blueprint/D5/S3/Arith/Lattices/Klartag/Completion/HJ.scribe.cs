using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class HJDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/HJ.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("HJ"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate hj to the stochastic ellipsoid construction.")),
            Node("claim-1", "log_le_six_rpow", "log le six rpow",
                "Real.log_le_rpow_div at ε = 1/6.", DescribeRole.Theorem),
            Node("claim-2", "log_cube_le", "log cube le",
                "(log n)³ ≤ 216·√n. Cubing log n ≤ 6·n^{1/6} and (n^{1/6})³ = n^{1/2} = √n.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
