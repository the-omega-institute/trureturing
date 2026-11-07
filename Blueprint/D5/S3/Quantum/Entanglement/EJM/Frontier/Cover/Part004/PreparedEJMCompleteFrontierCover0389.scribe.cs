using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0389Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0389.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0389",
        H("Original frontier context coverage 0389"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18674", "selected_cut_18674", "Selected cut at depth 13, code 287105, node 477415",
                "At remaining fuel 8 and original index 477415, selection on the full partial prefix of depth 13 and code 287105 returns the complete row with depth 13, base-four code 287105, original node 477415, kind 2, reserved field 0, 1889 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18721", "selected_cut_18721", "Selected cut at depth 12, code 71809, node 478780",
                "At remaining fuel 9 and original index 478780, selection on the full partial prefix of depth 12 and code 71809 returns the complete row with depth 12, base-four code 71809, original node 478780, kind 2, reserved field 0, 2089 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-71776-477472", "unmarked_context_12_71776_477472", "Unmarked parent at depth 12, code 71776",
                "The frontier Boolean is false at remaining fuel 9, original node 477472, the whole prefixCache at depth 12 and code 71776, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1121-478752", "unmarked_context_9_1121_478752", "Unmarked parent at depth 9, code 1121",
                "The frontier Boolean is false at remaining fuel 12, original node 478752, the whole prefixCache at depth 9 and code 1121, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-71776-477472", "node_context_12_71776_477472", "Original split at fuel 9 and node 477472",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 477415, 477461, 477471. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1121-478752", "node_context_9_1121_478752", "Original split at fuel 12 and node 478752",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 476485, 477376, 478127, 478751. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-287105-477415", "context_13_287105_477415", "Context at depth 13, code 287105, node 477415",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 287105 and original node 477415, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-71809-478780", "context_12_71809_478780", "Context at depth 12, code 71809, node 478780",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71809 and original node 478780, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
