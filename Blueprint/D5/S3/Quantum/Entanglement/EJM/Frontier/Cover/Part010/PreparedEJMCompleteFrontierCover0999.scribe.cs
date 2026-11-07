using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0999Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0999.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0999",
        H("Original frontier context coverage 0999"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47955", "selected_cut_47955", "Selected cut at depth 12, code 374820, node 435790",
                "At remaining fuel 9 and original index 435790, selection on the full partial prefix of depth 12 and code 374820 returns the complete row with depth 12, base-four code 374820, original node 435790, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48003", "selected_cut_48003", "Selected cut at depth 11, code 93741, node 1344935",
                "At remaining fuel 10 and original index 1344935, selection on the full partial prefix of depth 11 and code 93741 returns the complete row with depth 11, base-four code 93741, original node 1344935, kind 2, reserved field 0, 1785 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93705-1343356", "unmarked_context_11_93705_1343356", "Unmarked parent at depth 11, code 93705",
                "The frontier Boolean is false at remaining fuel 10, original node 1343356, the whole prefixCache at depth 11 and code 93705, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23433-1344850", "unmarked_context_10_23433_1344850", "Unmarked parent at depth 10, code 23433",
                "The frontier Boolean is false at remaining fuel 11, original node 1344850, the whole prefixCache at depth 10 and code 23433, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93705-1343356", "node_context_11_93705_1343356", "Original split at fuel 10 and node 1343356",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 1321747, 1343315, 1343355. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23433-1344850", "node_context_10_23433_1344850", "Original split at fuel 11 and node 1344850",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1344773, 1192826, 1344809, 1344849. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-374820-435790", "context_12_374820_435790", "Context at depth 12, code 374820, node 435790",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 374820 and original node 435790, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-93741-1344935", "context_11_93741_1344935", "Context at depth 11, code 93741, node 1344935",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93741 and original node 1344935, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
