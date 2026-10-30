using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0023Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0023.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0023",
        H("Original frontier context coverage 0023"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01106", "selected_cut_01106", "Selected cut at depth 13, code 17558, node 43161",
                "At remaining fuel 8 and original index 43161, selection on the full partial prefix of depth 13 and code 17558 returns the complete row with depth 13, base-four code 17558, original node 43161, kind 2, reserved field 0, 2485 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01153", "selected_cut_01153", "Selected cut at depth 13, code 17671, node 414",
                "At remaining fuel 8 and original index 414, selection on the full partial prefix of depth 13 and code 17671 returns the complete row with depth 13, base-four code 17671, original node 414, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-4389-43183", "unmarked_context_12_4389_43183", "Unmarked parent at depth 12, code 4389",
                "The frontier Boolean is false at remaining fuel 9, original node 43183, the whole prefixCache at depth 12 and code 4389, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-68-44134", "unmarked_context_9_68_44134", "Unmarked parent at depth 9, code 68",
                "The frontier Boolean is false at remaining fuel 12, original node 44134, the whole prefixCache at depth 9 and code 68, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-4389-43183", "node_context_12_4389_43183", "Original split at fuel 9 and node 43183",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 43086, 43131, 43161, 43182. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-68-44134", "node_context_9_68_44134", "Original split at fuel 12 and node 44134",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 41501, 42546, 44133, 3440. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-17558-43161", "context_13_17558_43161", "Context at depth 13, code 17558, node 43161",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 17558 and original node 43161, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-17671-414", "context_13_17671_414", "Context at depth 13, code 17671, node 414",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 17671 and original node 414, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
