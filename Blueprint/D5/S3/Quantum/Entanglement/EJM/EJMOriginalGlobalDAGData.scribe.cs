using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMOriginalGlobalDAGDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMOriginalGlobalDAGData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete original-domain EJM DAG input",
        H("Complete original-domain EJM DAG input"),
        Blocks(
            Paragraph(Text("The original 1,558,777 records retain their IDs, source-action pivots, literal split coordinates and all four children. This is untrusted input; no complete acceptance or minimum is asserted.")),
            Node("word", "word", "Decode one original 103-bit record",
                "The original index selects a 128-record literal chunk, then extracts exactly one 103-bit word.", DescribeRole.Definition),
            Node("nodes", "nodes", "Interpret the actual record at its actual fuel",
                "Bound and symmetry records retain their literal meanings. A split must agree with the actual original coordinate at the fuel depth; otherwise an identity cut rejects.", DescribeRole.Definition),
            Node("root", "root", "The complete original DAG root",
                "The root is the literal original record 1,558,776. Its global replay acceptance is a separate kernel obligation.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
