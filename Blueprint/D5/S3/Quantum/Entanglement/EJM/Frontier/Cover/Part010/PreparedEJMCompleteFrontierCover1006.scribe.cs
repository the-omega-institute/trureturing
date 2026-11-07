using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1006Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1006.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1006",
        H("Original frontier context coverage 1006"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48292", "selected_cut_48292", "Selected cut at depth 12, code 375835, node 1354440",
                "At remaining fuel 9 and original index 1354440, selection on the full partial prefix of depth 12 and code 375835 returns the complete row with depth 12, base-four code 375835, original node 1354440, kind 2, reserved field 0, 2809 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48339", "selected_cut_48339", "Selected cut at depth 11, code 93981, node 1356081",
                "At remaining fuel 10 and original index 1356081, selection on the full partial prefix of depth 11 and code 93981 returns the complete row with depth 11, base-four code 93981, original node 1356081, kind 2, reserved field 0, 3157 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93958-1354441", "unmarked_context_11_93958_1354441", "Unmarked parent at depth 11, code 93958",
                "The frontier Boolean is false at remaining fuel 10, original node 1354441, the whole prefixCache at depth 11 and code 93958, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23494-1355960", "unmarked_context_10_23494_1355960", "Unmarked parent at depth 10, code 23494",
                "The frontier Boolean is false at remaining fuel 11, original node 1355960, the whole prefixCache at depth 10 and code 23494, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93958-1354441", "node_context_11_93958_1354441", "Original split at fuel 10 and node 1354441",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 994572, 1354384, 806997, 1354440. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23494-1355960", "node_context_10_23494_1355960", "Original split at fuel 11 and node 1355960",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1355738, 1355834, 1355886, 1355959. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-375835-1354440", "context_12_375835_1354440", "Context at depth 12, code 375835, node 1354440",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 375835 and original node 1354440, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-93981-1356081", "context_11_93981_1356081", "Context at depth 11, code 93981, node 1356081",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93981 and original node 1356081, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
