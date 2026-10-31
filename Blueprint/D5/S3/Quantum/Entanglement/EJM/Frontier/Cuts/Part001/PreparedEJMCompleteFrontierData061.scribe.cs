using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cuts.Part001;

internal sealed class PreparedEJMCompleteFrontierData061Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cuts/Part001/PreparedEJMCompleteFrontierData061.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original cut table chunk 061",
        H("Original cut table chunk 061"),
        Blocks(
            Paragraph(Text("A CutTable is a binary search tree with lexicographic depth/code pivots. Every leaf stores a full CutRow: depth, kind, reserved field, original node index, full prefix code, subtree occurrence count and completion domain. The consumer pairs this exact tree with its Responses conjunction.")),
            Paragraph(Text("This chunk contains 256 leaves. The first stored row has depth 12, base-four code 93307, original node 735898, kind 2, reserved field 0, 3029 subtree occurrences and completion domain 65536; the last has depth 12, base-four code 93818, original node 419292, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536.")),
            Node("table-chunk061", "tableChunk061", "The complete literal table chunk 061",
                "The definition retains all 256 literal rows and every branch pivot. Stored depths range from 12 to 12, and original indices from 34034 to 753187. Lookup compares depth and code at each pivot and checks both fields at a leaf; metadata and semantic responses are separate conditions.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
