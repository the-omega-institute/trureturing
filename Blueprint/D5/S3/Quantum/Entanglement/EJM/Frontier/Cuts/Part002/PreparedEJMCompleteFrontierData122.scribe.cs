using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cuts.Part002;

internal sealed class PreparedEJMCompleteFrontierData122Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cuts/Part002/PreparedEJMCompleteFrontierData122.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original cut table chunk 122",
        H("Original cut table chunk 122"),
        Blocks(
            Paragraph(Text("A CutTable is a binary search tree with lexicographic depth/code pivots. Every leaf stores a full CutRow: depth, kind, reserved field, original node index, full prefix code, subtree occurrence count and completion domain. The consumer pairs this exact tree with its Responses conjunction.")),
            Paragraph(Text("This chunk contains 256 leaves. The first stored row has depth 13, base-four code 75193, original node 155945, kind 2, reserved field 0, 833 subtree occurrences and completion domain 16384; the last has depth 13, base-four code 81962, original node 168058, kind 2, reserved field 0, 1721 subtree occurrences and completion domain 16384.")),
            Node("table-chunk122", "tableChunk122", "The complete literal table chunk 122",
                "The definition retains all 256 literal rows and every branch pivot. Stored depths range from 13 to 13, and original indices from 3444 to 168058. Lookup compares depth and code at each pivot and checks both fields at a leaf; metadata and semantic responses are separate conditions.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
