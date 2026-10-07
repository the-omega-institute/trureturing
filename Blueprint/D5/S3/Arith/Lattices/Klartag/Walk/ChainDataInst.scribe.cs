using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class ChainDataInstDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/ChainDataInst.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Chain Data Inst"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate chain data inst to the stochastic ellipsoid construction.")),
            Node("claim-3", "chainData_of_params", "chain Data of params",
                "ChainData from the chain's parameters.", DescribeRole.Definition),
            Node("claim-4", "exists_good_line_of_params", "exists good line of params",
                "The composite. From the chain's parameters to §5's single line g.", DescribeRole.Theorem),
            Node("claim-6", "transfer_det_of_eq68", "transfer det of eq68",
                "The determinant condition, in Klartag's eq. (68) form. With |det B| = κ_n the transfer's hypothesis reduces to √(det A)·(c·m²) ≤ 1: the chain's det A_T ≤ C/n⁴ with c ≤ C^{-1/2}.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
