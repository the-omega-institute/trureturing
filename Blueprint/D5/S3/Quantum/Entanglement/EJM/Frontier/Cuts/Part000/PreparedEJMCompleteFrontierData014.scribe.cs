using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cuts.Part000;

internal sealed class PreparedEJMCompleteFrontierData014Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cuts/Part000/PreparedEJMCompleteFrontierData014.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original cut table chunk 014",
        H("Original cut table chunk 014"),
        Blocks(
            Paragraph(Text("A CutTable is a binary search tree with lexicographic depth/code pivots. Every leaf stores a full CutRow: depth, kind, reserved field, original node index, full prefix code, subtree occurrence count and completion domain. The consumer pairs this exact tree with its Responses conjunction.")),
            Paragraph(Text("This chunk contains 256 leaves. The first stored row has depth 11, base-four code 70298, original node 900363, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144; the last has depth 11, base-four code 71915, original node 949287, kind 2, reserved field 0, 3045 subtree occurrences and completion domain 262144.")),
            Node("table-chunk014", "tableChunk014", "The complete literal table chunk 014",
                "The definition retains all 256 literal rows and every branch pivot. Stored depths range from 11 to 11, and original indices from 1736 to 949287. Lookup compares depth and code at each pivot and checks both fields at a leaf; metadata and semantic responses are separate conditions.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
