using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0173Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0173.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0173",
        H("Original frontier context coverage 0173"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08308", "selected_cut_08308", "Selected cut at depth 13, code 91567, node 233363",
                "At remaining fuel 8 and original index 233363, selection on the full partial prefix of depth 13 and code 91567 returns the complete row with depth 13, base-four code 91567, original node 233363, kind 2, reserved field 0, 1265 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08354", "selected_cut_08354", "Selected cut at depth 12, code 22919, node 234315",
                "At remaining fuel 9 and original index 234315, selection on the full partial prefix of depth 12 and code 22919 returns the complete row with depth 12, base-four code 22919, original node 234315, kind 2, reserved field 0, 2233 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22891-233364", "unmarked_context_12_22891_233364", "Unmarked parent at depth 12, code 22891",
                "The frontier Boolean is false at remaining fuel 9, original node 233364, the whole prefixCache at depth 12 and code 22891, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5728-234207", "unmarked_context_11_5728_234207", "Unmarked parent at depth 11, code 5728",
                "The frontier Boolean is false at remaining fuel 10, original node 234207, the whole prefixCache at depth 11 and code 5728, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22891-233364", "node_context_12_22891_233364", "Original split at fuel 9 and node 233364",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 233322, 233354, 233363. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5728-234207", "node_context_11_5728_234207", "Original split at fuel 10 and node 234207",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 234127, 234153, 234182, 234206. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-91567-233363", "context_13_91567_233363", "Context at depth 13, code 91567, node 233363",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 91567 and original node 233363, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-22919-234315", "context_12_22919_234315", "Context at depth 12, code 22919, node 234315",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22919 and original node 234315, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
