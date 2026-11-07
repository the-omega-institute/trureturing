using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0139Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0139.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0139",
        H("Original frontier context coverage 0139"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06675", "selected_cut_06675", "Selected cut at depth 13, code 87225, node 198458",
                "At remaining fuel 8 and original index 198458, selection on the full partial prefix of depth 13 and code 87225 returns the complete row with depth 13, base-four code 87225, original node 198458, kind 2, reserved field 0, 2525 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06722", "selected_cut_06722", "Selected cut at depth 13, code 87386, node 199225",
                "At remaining fuel 8 and original index 199225, selection on the full partial prefix of depth 13 and code 87386 returns the complete row with depth 13, base-four code 87386, original node 199225, kind 2, reserved field 0, 1869 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-21806-198492", "unmarked_context_12_21806_198492", "Unmarked parent at depth 12, code 21806",
                "The frontier Boolean is false at remaining fuel 9, original node 198492, the whole prefixCache at depth 12 and code 21806, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5460-199179", "unmarked_context_11_5460_199179", "Unmarked parent at depth 11, code 5460",
                "The frontier Boolean is false at remaining fuel 10, original node 199179, the whole prefixCache at depth 11 and code 5460, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-21806-198492", "node_context_12_21806_198492", "Original split at fuel 9 and node 198492",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 198417, 198458, 198481, 198491. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5460-199179", "node_context_11_5460_199179", "Original split at fuel 10 and node 199179",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 199119, 126371, 199178, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-87225-198458", "context_13_87225_198458", "Context at depth 13, code 87225, node 198458",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 87225 and original node 198458, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-87386-199225", "context_13_87386_199225", "Context at depth 13, code 87386, node 199225",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 87386 and original node 199225, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
