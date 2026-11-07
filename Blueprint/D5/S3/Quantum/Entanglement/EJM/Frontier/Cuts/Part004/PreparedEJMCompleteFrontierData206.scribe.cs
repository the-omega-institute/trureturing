using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cuts.Part004;

internal sealed class PreparedEJMCompleteFrontierData206Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cuts/Part004/PreparedEJMCompleteFrontierData206.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original cut table chunk 206",
        H("Original cut table chunk 206"),
        Blocks(
            Paragraph(Text("A CutTable is a binary search tree with lexicographic depth/code pivots. Every leaf stores a full CutRow: depth, kind, reserved field, original node index, full prefix code, subtree occurrence count and completion domain. The consumer pairs this exact tree with its Responses conjunction.")),
            Paragraph(Text("This chunk contains 131 leaves. The first stored row has depth 14, base-four code 1156037, original node 500991, kind 2, reserved field 0, 1129 subtree occurrences and completion domain 4096; the last has depth 14, base-four code 1765523, original node 861921, kind 2, reserved field 0, 973 subtree occurrences and completion domain 4096.")),
            Node("table-chunk206", "tableChunk206", "The complete literal table chunk 206",
                "The definition retains all 131 literal rows and every branch pivot. Stored depths range from 14 to 14, and original indices from 500991 to 861921. Lookup compares depth and code at each pivot and checks both fields at a leaf; metadata and semantic responses are separate conditions.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
