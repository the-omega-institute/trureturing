using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0581Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0581.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0581",
        H("Original frontier context coverage 0581"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27892", "selected_cut_27892", "Selected cut at depth 13, code 367768, node 704762",
                "At remaining fuel 8 and original index 704762, selection on the full partial prefix of depth 13 and code 367768 returns the complete row with depth 13, base-four code 367768, original node 704762, kind 2, reserved field 0, 945 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27939", "selected_cut_27939", "Selected cut at depth 13, code 367818, node 705646",
                "At remaining fuel 8 and original index 705646, selection on the full partial prefix of depth 13 and code 367818 returns the complete row with depth 13, base-four code 367818, original node 705646, kind 2, reserved field 0, 1465 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-91941-704748", "unmarked_context_12_91941_704748", "Unmarked parent at depth 12, code 91941",
                "The frontier Boolean is false at remaining fuel 9, original node 704748, the whole prefixCache at depth 12 and code 91941, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-91953-705598", "unmarked_context_12_91953_705598", "Unmarked parent at depth 12, code 91953",
                "The frontier Boolean is false at remaining fuel 9, original node 705598, the whole prefixCache at depth 12 and code 91953, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-91941-704748", "node_context_12_91941_704748", "Original split at fuel 9 and node 704748",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 704706, 704728, 704742, 704747. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-91953-705598", "node_context_12_91953_705598", "Original split at fuel 9 and node 705598",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 705533, 705563, 705587, 705597. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-91941-704748", "context_12_91941_704748", "Context at depth 12, code 91941, node 704748",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 91941 and original node 704748, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_367764_704706, context_13_367765_704728, context_13_367766_704742, context_13_367767_704747.", DescribeRole.Theorem),
            Node("context-13-367818-705646", "context_13_367818_705646", "Context at depth 13, code 367818, node 705646",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 367818 and original node 705646, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
