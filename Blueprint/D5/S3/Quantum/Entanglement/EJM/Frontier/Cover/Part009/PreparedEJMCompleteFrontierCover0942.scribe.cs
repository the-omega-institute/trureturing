using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0942Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0942.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0942",
        H("Original frontier context coverage 0942"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45220", "selected_cut_45220", "Selected cut at depth 12, code 356149, node 402280",
                "At remaining fuel 9 and original index 402280, selection on the full partial prefix of depth 12 and code 356149 returns the complete row with depth 12, base-four code 356149, original node 402280, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45267", "selected_cut_45267", "Selected cut at depth 10, code 22269, node 1252250",
                "At remaining fuel 11 and original index 1252250, selection on the full partial prefix of depth 10 and code 22269 returns the complete row with depth 10, base-four code 22269, original node 1252250, kind 2, reserved field 0, 1793 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-89037-1250515", "unmarked_context_11_89037_1250515", "Unmarked parent at depth 11, code 89037",
                "The frontier Boolean is false at remaining fuel 10, original node 1250515, the whole prefixCache at depth 11 and code 89037, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5566-1252154", "unmarked_context_9_5566_1252154", "Unmarked parent at depth 9, code 5566",
                "The frontier Boolean is false at remaining fuel 12, original node 1252154, the whole prefixCache at depth 9 and code 5566, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-89037-1250515", "node_context_11_89037_1250515", "Original split at fuel 10 and node 1250515",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1250420, 402280, 1250466, 1250514. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5566-1252154", "node_context_9_5566_1252154", "Original split at fuel 12 and node 1252154",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1251795, 1251972, 1252040, 1252153. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-356149-402280", "context_12_356149_402280", "Context at depth 12, code 356149, node 402280",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 356149 and original node 402280, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-22269-1252250", "context_10_22269_1252250", "Context at depth 10, code 22269, node 1252250",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 22269 and original node 1252250, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
