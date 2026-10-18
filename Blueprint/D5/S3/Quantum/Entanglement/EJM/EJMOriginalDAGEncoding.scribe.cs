using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMOriginalDAGEncodingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMOriginalDAGEncoding.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced storage for original DAG words",
        H("Balanced storage for original DAG words"),
        Blocks(
            Paragraph(Text("This module stores untrusted words only. Missing lookup returns zero and never establishes acceptance; the full replay must check every reached bound, action and split.")),
            Node("PackedTree", "PackedTree", "Balanced literal word data",
                "Each tree node stores its original chunk index, literal word and both subtrees.", DescribeRole.Definition),
            Node("get", "get", "Look up the proposed original chunk",
                "The exact chunk index selects the word through the balanced tree. An empty tree returns zero, so lookup alone supplies no correctness premise.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
