using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cuts.Part001;

internal sealed class PreparedEJMCompleteFrontierData054Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cuts/Part001/PreparedEJMCompleteFrontierData054.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original cut table chunk 054",
        H("Original cut table chunk 054"),
        Blocks(
            Paragraph(Text("A CutTable is a binary search tree with lexicographic depth/code pivots. Every leaf stores a full CutRow: depth, kind, reserved field, original node index, full prefix code, subtree occurrence count and completion domain. The consumer pairs this exact tree with its Responses conjunction.")),
            Paragraph(Text("This chunk contains 256 leaves. The first stored row has depth 12, base-four code 76660, original node 601711, kind 2, reserved field 0, 3485 subtree occurrences and completion domain 65536; the last has depth 12, base-four code 77179, original node 619496, kind 2, reserved field 0, 3229 subtree occurrences and completion domain 65536.")),
            Node("table-chunk054", "tableChunk054", "The complete literal table chunk 054",
                "The definition retains all 256 literal rows and every branch pivot. Stored depths range from 12 to 12, and original indices from 34034 to 619496. Lookup compares depth and code at each pivot and checks both fields at a leaf; metadata and semantic responses are separate conditions.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
