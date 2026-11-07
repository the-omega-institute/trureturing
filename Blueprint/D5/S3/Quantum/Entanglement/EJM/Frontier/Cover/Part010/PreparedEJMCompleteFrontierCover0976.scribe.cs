using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0976Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0976.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0976",
        H("Original frontier context coverage 0976"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46852", "selected_cut_46852", "Selected cut at depth 12, code 371743, node 1308149",
                "At remaining fuel 9 and original index 1308149, selection on the full partial prefix of depth 12 and code 371743 returns the complete row with depth 12, base-four code 371743, original node 1308149, kind 2, reserved field 0, 3181 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46899", "selected_cut_46899", "Selected cut at depth 12, code 371814, node 1309764",
                "At remaining fuel 9 and original index 1309764, selection on the full partial prefix of depth 12 and code 371814 returns the complete row with depth 12, base-four code 371814, original node 1309764, kind 2, reserved field 0, 1661 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92935-1308150", "unmarked_context_11_92935_1308150", "Unmarked parent at depth 11, code 92935",
                "The frontier Boolean is false at remaining fuel 10, original node 1308150, the whole prefixCache at depth 11 and code 92935, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23236-1309645", "unmarked_context_10_23236_1309645", "Unmarked parent at depth 10, code 23236",
                "The frontier Boolean is false at remaining fuel 11, original node 1309645, the whole prefixCache at depth 10 and code 23236, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92935-1308150", "node_context_11_92935_1308150", "Original split at fuel 10 and node 1308150",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1307971, 1308028, 1308090, 1308149. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23236-1309645", "node_context_10_23236_1309645", "Original split at fuel 11 and node 1309645",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1309318, 1309458, 1309557, 1309644. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-371743-1308149", "context_12_371743_1308149", "Context at depth 12, code 371743, node 1308149",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 371743 and original node 1308149, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-371814-1309764", "context_12_371814_1309764", "Context at depth 12, code 371814, node 1309764",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 371814 and original node 1309764, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
