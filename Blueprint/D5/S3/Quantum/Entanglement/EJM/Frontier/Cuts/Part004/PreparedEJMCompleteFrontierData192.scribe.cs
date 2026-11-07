using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cuts.Part004;

internal sealed class PreparedEJMCompleteFrontierData192Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cuts/Part004/PreparedEJMCompleteFrontierData192.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original cut table chunk 192",
        H("Original cut table chunk 192"),
        Blocks(
            Paragraph(Text("A CutTable is a binary search tree with lexicographic depth/code pivots. Every leaf stores a full CutRow: depth, kind, reserved field, original node index, full prefix code, subtree occurrence count and completion domain. The consumer pairs this exact tree with its Responses conjunction.")),
            Paragraph(Text("This chunk contains 256 leaves. The first stored row has depth 13, base-four code 433334, original node 832916, kind 2, reserved field 0, 957 subtree occurrences and completion domain 16384; the last has depth 13, base-four code 439398, original node 846369, kind 2, reserved field 0, 1577 subtree occurrences and completion domain 16384.")),
            Node("table-chunk192", "tableChunk192", "The complete literal table chunk 192",
                "The definition retains all 256 literal rows and every branch pivot. Stored depths range from 13 to 13, and original indices from 3444 to 846369. Lookup compares depth and code at each pivot and checks both fields at a leaf; metadata and semantic responses are separate conditions.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
