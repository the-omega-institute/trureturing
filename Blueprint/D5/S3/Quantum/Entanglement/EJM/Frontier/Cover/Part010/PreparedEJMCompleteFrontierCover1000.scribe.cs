using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1000Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1000.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1000",
        H("Original frontier context coverage 1000"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48004", "selected_cut_48004", "Selected cut at depth 11, code 93742, node 1344955",
                "At remaining fuel 10 and original index 1344955, selection on the full partial prefix of depth 11 and code 93742 returns the complete row with depth 11, base-four code 93742, original node 1344955, kind 2, reserved field 0, 1385 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48051", "selected_cut_48051", "Selected cut at depth 12, code 375087, node 1346300",
                "At remaining fuel 9 and original index 1346300, selection on the full partial prefix of depth 12 and code 375087 returns the complete row with depth 12, base-four code 375087, original node 1346300, kind 2, reserved field 0, 1969 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23435-1344963", "unmarked_context_10_23435_1344963", "Unmarked parent at depth 10, code 23435",
                "The frontier Boolean is false at remaining fuel 11, original node 1344963, the whole prefixCache at depth 10 and code 23435, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-93771-1346301", "unmarked_context_11_93771_1346301", "Unmarked parent at depth 11, code 93771",
                "The frontier Boolean is false at remaining fuel 10, original node 1346301, the whole prefixCache at depth 11 and code 93771, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23435-1344963", "node_context_10_23435_1344963", "Original split at fuel 11 and node 1344963",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1344900, 1344935, 1344955, 1344962. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-93771-1346301", "node_context_11_93771_1346301", "Original split at fuel 10 and node 1346301",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1346198, 1346237, 1346273, 1346300. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-93742-1344955", "context_11_93742_1344955", "Context at depth 11, code 93742, node 1344955",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93742 and original node 1344955, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-93771-1346301", "context_11_93771_1346301", "Context at depth 11, code 93771, node 1346301",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93771 and original node 1346301, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_375084_1346198, context_12_375085_1346237, context_12_375086_1346273, context_12_375087_1346300.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
