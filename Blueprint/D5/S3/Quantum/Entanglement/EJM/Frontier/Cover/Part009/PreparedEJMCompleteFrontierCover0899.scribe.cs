using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0899Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0899.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0899",
        H("Original frontier context coverage 0899"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43155", "selected_cut_43155", "Selected cut at depth 12, code 339489, node 1179875",
                "At remaining fuel 9 and original index 1179875, selection on the full partial prefix of depth 12 and code 339489 returns the complete row with depth 12, base-four code 339489, original node 1179875, kind 2, reserved field 0, 3081 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43203", "selected_cut_43203", "Selected cut at depth 12, code 339555, node 1181273",
                "At remaining fuel 9 and original index 1181273, selection on the full partial prefix of depth 12 and code 339555 returns the complete row with depth 12, base-four code 339555, original node 1181273, kind 2, reserved field 0, 2157 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84872-1179992", "unmarked_context_11_84872_1179992", "Unmarked parent at depth 11, code 84872",
                "The frontier Boolean is false at remaining fuel 10, original node 1179992, the whole prefixCache at depth 11 and code 84872, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21220-1181136", "unmarked_context_10_21220_1181136", "Unmarked parent at depth 10, code 21220",
                "The frontier Boolean is false at remaining fuel 11, original node 1181136, the whole prefixCache at depth 10 and code 21220, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84872-1179992", "node_context_11_84872_1179992", "Original split at fuel 10 and node 1179992",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1179875, 1179920, 1179991. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21220-1181136", "node_context_10_21220_1181136", "Original split at fuel 11 and node 1181136",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1180866, 1180979, 1181042, 1181135. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-339489-1179875", "context_12_339489_1179875", "Context at depth 12, code 339489, node 1179875",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 339489 and original node 1179875, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-339555-1181273", "context_12_339555_1181273", "Context at depth 12, code 339555, node 1181273",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 339555 and original node 1181273, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
