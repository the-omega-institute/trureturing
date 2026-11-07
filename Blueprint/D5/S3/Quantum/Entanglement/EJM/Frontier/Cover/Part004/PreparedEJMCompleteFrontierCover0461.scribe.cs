using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0461Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0461.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0461",
        H("Original frontier context coverage 0461"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22131", "selected_cut_22131", "Selected cut at depth 13, code 302109, node 564033",
                "At remaining fuel 8 and original index 564033, selection on the full partial prefix of depth 13 and code 302109 returns the complete row with depth 13, base-four code 302109, original node 564033, kind 2, reserved field 0, 3021 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22178", "selected_cut_22178", "Selected cut at depth 13, code 302180, node 565405",
                "At remaining fuel 8 and original index 565405, selection on the full partial prefix of depth 13 and code 302180 returns the complete row with depth 13, base-four code 302180, original node 565405, kind 2, reserved field 0, 1537 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75527-564076", "unmarked_context_12_75527_564076", "Unmarked parent at depth 12, code 75527",
                "The frontier Boolean is false at remaining fuel 9, original node 564076, the whole prefixCache at depth 12 and code 75527, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-75544-565376", "unmarked_context_12_75544_565376", "Unmarked parent at depth 12, code 75544",
                "The frontier Boolean is false at remaining fuel 9, original node 565376, the whole prefixCache at depth 12 and code 75544, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75527-564076", "node_context_12_75527_564076", "Original split at fuel 9 and node 564076",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 563986, 564033, 564070, 564075. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-75544-565376", "node_context_12_75544_565376", "Original split at fuel 9 and node 565376",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 565267, 565319, 565362, 565375. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-302109-564033", "context_13_302109_564033", "Context at depth 13, code 302109, node 564033",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 302109 and original node 564033, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-302180-565405", "context_13_302180_565405", "Context at depth 13, code 302180, node 565405",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 302180 and original node 565405, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
