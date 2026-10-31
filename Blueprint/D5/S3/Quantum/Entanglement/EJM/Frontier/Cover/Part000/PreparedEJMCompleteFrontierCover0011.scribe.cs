using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0011Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0011.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0011",
        H("Original frontier context coverage 0011"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00530", "selected_cut_00530", "Selected cut at depth 13, code 6167, node 24534",
                "At remaining fuel 8 and original index 24534, selection on the full partial prefix of depth 13 and code 6167 returns the complete row with depth 13, base-four code 6167, original node 24534, kind 2, reserved field 0, 1317 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00577", "selected_cut_00577", "Selected cut at depth 14, code 24772, node 25924",
                "At remaining fuel 7 and original index 25924, selection on the full partial prefix of depth 14 and code 24772 returns the complete row with depth 14, base-four code 24772, original node 25924, kind 2, reserved field 0, 1701 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-1541-24535", "unmarked_context_12_1541_24535", "Unmarked parent at depth 12, code 1541",
                "The frontier Boolean is false at remaining fuel 9, original node 24535, the whole prefixCache at depth 12 and code 1541, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-386-25818", "unmarked_context_11_386_25818", "Unmarked parent at depth 11, code 386",
                "The frontier Boolean is false at remaining fuel 10, original node 25818, the whole prefixCache at depth 11 and code 386, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-1541-24535", "node_context_12_1541_24535", "Original split at fuel 9 and node 24535",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 24415, 24469, 24507, 24534. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-386-25818", "node_context_11_386_25818", "Original split at fuel 10 and node 25818",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 3161, 25230, 25601, 25817. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-6167-24534", "context_13_6167_24534", "Context at depth 13, code 6167, node 24534",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 6167 and original node 24534, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-24772-25924", "context_14_24772_25924", "Context at depth 14, code 24772, node 25924",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 24772 and original node 25924, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
