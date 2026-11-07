using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0547Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0547.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0547",
        H("Original frontier context coverage 0547"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26259", "selected_cut_26259", "Selected cut at depth 12, code 88662, node 664108",
                "At remaining fuel 9 and original index 664108, selection on the full partial prefix of depth 12 and code 88662 returns the complete row with depth 12, base-four code 88662, original node 664108, kind 2, reserved field 0, 3421 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26306", "selected_cut_26306", "Selected cut at depth 12, code 88706, node 665447",
                "At remaining fuel 9 and original index 665447, selection on the full partial prefix of depth 12 and code 88706 returns the complete row with depth 12, base-four code 88706, original node 665447, kind 2, reserved field 0, 1601 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-22165-664153", "unmarked_context_11_22165_664153", "Unmarked parent at depth 11, code 22165",
                "The frontier Boolean is false at remaining fuel 10, original node 664153, the whole prefixCache at depth 11 and code 22165, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1385-665385", "unmarked_context_9_1385_665385", "Unmarked parent at depth 9, code 1385",
                "The frontier Boolean is false at remaining fuel 12, original node 665385, the whole prefixCache at depth 9 and code 1385, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-22165-664153", "node_context_11_22165_664153", "Original split at fuel 10 and node 664153",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 664058, 642341, 664108, 664152. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1385-665385", "node_context_9_1385_665385", "Original split at fuel 12 and node 665385",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 663860, 664398, 664882, 665384. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-88662-664108", "context_12_88662_664108", "Context at depth 12, code 88662, node 664108",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 88662 and original node 664108, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-88706-665447", "context_12_88706_665447", "Context at depth 12, code 88706, node 665447",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 88706 and original node 665447, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
