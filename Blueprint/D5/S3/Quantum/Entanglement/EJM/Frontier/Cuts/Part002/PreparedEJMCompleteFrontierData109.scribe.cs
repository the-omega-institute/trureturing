using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cuts.Part002;

internal sealed class PreparedEJMCompleteFrontierData109Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cuts/Part002/PreparedEJMCompleteFrontierData109.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original cut table chunk 109",
        H("Original cut table chunk 109"),
        Blocks(
            Paragraph(Text("A CutTable is a binary search tree with lexicographic depth/code pivots. Every leaf stores a full CutRow: depth, kind, reserved field, original node index, full prefix code, subtree occurrence count and completion domain. The consumer pairs this exact tree with its Responses conjunction.")),
            Paragraph(Text("This chunk contains 256 leaves. The first stored row has depth 12, base-four code 441138, original node 1455342, kind 2, reserved field 0, 1537 subtree occurrences and completion domain 65536; the last has depth 13, base-four code 1182, original node 10474, kind 2, reserved field 0, 2121 subtree occurrences and completion domain 16384.")),
            Node("table-chunk109", "tableChunk109", "The complete literal table chunk 109",
                "The definition retains all 256 literal rows and every branch pivot. Stored depths range from 12 to 13, and original indices from 414 to 1517760. Lookup compares depth and code at each pivot and checks both fields at a leaf; metadata and semantic responses are separate conditions.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
