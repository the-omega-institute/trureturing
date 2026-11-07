using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cuts.Part004;

internal sealed class PreparedEJMCompleteFrontierData205Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cuts/Part004/PreparedEJMCompleteFrontierData205.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original cut table chunk 205",
        H("Original cut table chunk 205"),
        Blocks(
            Paragraph(Text("A CutTable is a binary search tree with lexicographic depth/code pivots. Every leaf stores a full CutRow: depth, kind, reserved field, original node index, full prefix code, subtree occurrence count and completion domain. The consumer pairs this exact tree with its Responses conjunction.")),
            Paragraph(Text("This chunk contains 256 leaves. The first stored row has depth 14, base-four code 438513, original node 378873, kind 2, reserved field 0, 1789 subtree occurrences and completion domain 4096; the last has depth 14, base-four code 1156036, original node 500944, kind 2, reserved field 0, 1125 subtree occurrences and completion domain 4096.")),
            Node("table-chunk205", "tableChunk205", "The complete literal table chunk 205",
                "The definition retains all 256 literal rows and every branch pivot. Stored depths range from 14 to 14, and original indices from 291 to 500944. Lookup compares depth and code at each pivot and checks both fields at a leaf; metadata and semantic responses are separate conditions.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
