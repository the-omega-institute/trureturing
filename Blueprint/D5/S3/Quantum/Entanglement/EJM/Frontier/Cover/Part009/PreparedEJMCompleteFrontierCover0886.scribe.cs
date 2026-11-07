using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0886Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0886.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0886",
        H("Original frontier context coverage 0886"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42531", "selected_cut_42531", "Selected cut at depth 12, code 338211, node 1162288",
                "At remaining fuel 9 and original index 1162288, selection on the full partial prefix of depth 12 and code 338211 returns the complete row with depth 12, base-four code 338211, original node 1162288, kind 2, reserved field 0, 2129 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42578", "selected_cut_42578", "Selected cut at depth 12, code 338291, node 1163349",
                "At remaining fuel 9 and original index 1163349, selection on the full partial prefix of depth 12 and code 338291 returns the complete row with depth 12, base-four code 338291, original node 1163349, kind 2, reserved field 0, 1809 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84552-1162289", "unmarked_context_11_84552_1162289", "Unmarked parent at depth 11, code 84552",
                "The frontier Boolean is false at remaining fuel 10, original node 1162289, the whole prefixCache at depth 11 and code 84552, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84572-1163350", "unmarked_context_11_84572_1163350", "Unmarked parent at depth 11, code 84572",
                "The frontier Boolean is false at remaining fuel 10, original node 1163350, the whole prefixCache at depth 11 and code 84572, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84552-1162289", "node_context_11_84552_1162289", "Original split at fuel 10 and node 1162289",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1162226, 1162257, 1162288. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84572-1163350", "node_context_11_84572_1163350", "Original split at fuel 10 and node 1163350",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1163289, 355230, 1163317, 1163349. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-338211-1162288", "context_12_338211_1162288", "Context at depth 12, code 338211, node 1162288",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 338211 and original node 1162288, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-84572-1163350", "context_11_84572_1163350", "Context at depth 11, code 84572, node 1163350",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84572 and original node 1163350, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_338288_1163289, context_12_338289_355230, context_12_338290_1163317, context_12_338291_1163349.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
