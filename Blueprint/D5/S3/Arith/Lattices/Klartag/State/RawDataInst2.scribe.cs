using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.State;

internal sealed class RawDataInst2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric matrix state invariants and padded driving laws.",
        H("Raw Data Inst2"),
        Blocks(
            Paragraph(Text("Symmetric matrix state invariants and padded driving laws. The results below relate raw data inst2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "idUT", "id UT",
                "The identity matrix in Frobenius coordinates.", DescribeRole.Definition),
            Node("claim-4", "inner_idUT", "inner id UT",
                "⟪Id, q x⟫ = |x|².", DescribeRole.Theorem),
            Node("claim-5", "A0C", "A0C",
                "The chain's initial state, Klartag's a₀·Id (eq. 61).", DescribeRole.Definition),
            Node("claim-6", "xOf", "x Of",
                "The scaled lattice point, as a plain coordinate vector.", DescribeRole.Definition),
            Node("claim-8", "qC", "q C",
                "The chain's constraint vector at the scaled lattice point.", DescribeRole.Definition),
            Node("claim-11", "normData_qC", "norm Data q C",
                "NormData for the chain's own data — both fields, for any W.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
