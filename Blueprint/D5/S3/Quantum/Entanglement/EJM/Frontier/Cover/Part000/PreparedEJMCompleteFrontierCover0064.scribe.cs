using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0064Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0064.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0064",
        H("Original frontier context coverage 0064"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03074", "selected_cut_03074", "Selected cut at depth 13, code 26885, node 95283",
                "At remaining fuel 8 and original index 95283, selection on the full partial prefix of depth 13 and code 26885 returns the complete row with depth 13, base-four code 26885, original node 95283, kind 2, reserved field 0, 3733 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03122", "selected_cut_03122", "Selected cut at depth 13, code 26936, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 26936 returns the complete row with depth 13, base-four code 26936, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-6721-95326", "unmarked_context_12_6721_95326", "Unmarked parent at depth 12, code 6721",
                "The frontier Boolean is false at remaining fuel 9, original node 95326, the whole prefixCache at depth 12 and code 6721, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-6733-97001", "unmarked_context_12_6733_97001", "Unmarked parent at depth 12, code 6733",
                "The frontier Boolean is false at remaining fuel 9, original node 97001, the whole prefixCache at depth 12 and code 6733, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-6721-95326", "node_context_12_6721_95326", "Original split at fuel 9 and node 95326",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 95283, 95309, 95325. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-6733-97001", "node_context_12_6733_97001", "Original split at fuel 9 and node 97001",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 96935, 96979, 97000. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-26885-95283", "context_13_26885_95283", "Context at depth 13, code 26885, node 95283",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 26885 and original node 95283, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-26936-3444", "context_13_26936_3444", "Context at depth 13, code 26936, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 26936 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
