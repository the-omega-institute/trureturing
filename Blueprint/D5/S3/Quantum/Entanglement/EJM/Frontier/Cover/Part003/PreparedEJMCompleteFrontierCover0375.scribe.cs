using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0375Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0375.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0375",
        H("Original frontier context coverage 0375"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18002", "selected_cut_18002", "Selected cut at depth 13, code 284708, node 461745",
                "At remaining fuel 8 and original index 461745, selection on the full partial prefix of depth 13 and code 284708 returns the complete row with depth 13, base-four code 284708, original node 461745, kind 2, reserved field 0, 2865 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18049", "selected_cut_18049", "Selected cut at depth 13, code 284755, node 463173",
                "At remaining fuel 8 and original index 463173, selection on the full partial prefix of depth 13 and code 284755 returns the complete row with depth 13, base-four code 284755, original node 463173, kind 2, reserved field 0, 1409 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-71177-461818", "unmarked_context_12_71177_461818", "Unmarked parent at depth 12, code 71177",
                "The frontier Boolean is false at remaining fuel 9, original node 461818, the whole prefixCache at depth 12 and code 71177, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-71188-463174", "unmarked_context_12_71188_463174", "Unmarked parent at depth 12, code 71188",
                "The frontier Boolean is false at remaining fuel 9, original node 463174, the whole prefixCache at depth 12 and code 71188, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-71177-461818", "node_context_12_71177_461818", "Original split at fuel 9 and node 461818",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 461745, 461782, 461802, 461817. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-71188-463174", "node_context_12_71188_463174", "Original split at fuel 9 and node 463174",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 463044, 463110, 463141, 463173. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-284708-461745", "context_13_284708_461745", "Context at depth 13, code 284708, node 461745",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 284708 and original node 461745, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-71188-463174", "context_12_71188_463174", "Context at depth 12, code 71188, node 463174",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71188 and original node 463174, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_284752_463044, context_13_284753_463110, context_13_284754_463141, context_13_284755_463173.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
