using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0157Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0157.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0157",
        H("Original frontier context coverage 0157"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07538", "selected_cut_07538", "Selected cut at depth 13, code 90305, node 218253",
                "At remaining fuel 8 and original index 218253, selection on the full partial prefix of depth 13 and code 90305 returns the complete row with depth 13, base-four code 90305, original node 218253, kind 2, reserved field 0, 3589 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07586", "selected_cut_07586", "Selected cut at depth 13, code 90353, node 219136",
                "At remaining fuel 8 and original index 219136, selection on the full partial prefix of depth 13 and code 90353 returns the complete row with depth 13, base-four code 90353, original node 219136, kind 2, reserved field 0, 2317 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22576-218302", "unmarked_context_12_22576_218302", "Unmarked parent at depth 12, code 22576",
                "The frontier Boolean is false at remaining fuel 9, original node 218302, the whole prefixCache at depth 12 and code 22576, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5646-219096", "unmarked_context_11_5646_219096", "Unmarked parent at depth 11, code 5646",
                "The frontier Boolean is false at remaining fuel 10, original node 219096, the whole prefixCache at depth 11 and code 5646, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22576-218302", "node_context_12_22576_218302", "Original split at fuel 9 and node 218302",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 218195, 218253, 218289, 218301. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5646-219096", "node_context_11_5646_219096", "Original split at fuel 10 and node 219096",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 218868, 218931, 219016, 219095. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-90305-218253", "context_13_90305_218253", "Context at depth 13, code 90305, node 218253",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 90305 and original node 218253, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-90353-219136", "context_13_90353_219136", "Context at depth 13, code 90353, node 219136",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 90353 and original node 219136, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
