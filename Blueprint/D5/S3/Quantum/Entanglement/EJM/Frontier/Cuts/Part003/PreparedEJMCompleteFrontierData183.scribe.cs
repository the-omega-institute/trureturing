using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cuts.Part003;

internal sealed class PreparedEJMCompleteFrontierData183Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cuts/Part003/PreparedEJMCompleteFrontierData183.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original cut table chunk 183",
        H("Original cut table chunk 183"),
        Blocks(
            Paragraph(Text("A CutTable is a binary search tree with lexicographic depth/code pivots. Every leaf stores a full CutRow: depth, kind, reserved field, original node index, full prefix code, subtree occurrence count and completion domain. The consumer pairs this exact tree with its Responses conjunction.")),
            Paragraph(Text("This chunk contains 256 leaves. The first stored row has depth 13, base-four code 371805, original node 724577, kind 2, reserved field 0, 2105 subtree occurrences and completion domain 16384; the last has depth 13, base-four code 372972, original node 733654, kind 2, reserved field 0, 129 subtree occurrences and completion domain 16384.")),
            Node("table-chunk183", "tableChunk183", "The complete literal table chunk 183",
                "The definition retains all 256 literal rows and every branch pivot. Stored depths range from 13 to 13, and original indices from 724577 to 733654. Lookup compares depth and code at each pivot and checks both fields at a leaf; metadata and semantic responses are separate conditions.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
