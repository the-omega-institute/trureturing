using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0697Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0697.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0697",
        H("Original frontier context coverage 0697"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33460", "selected_cut_33460", "Selected cut at depth 12, code 110245, node 861197",
                "At remaining fuel 9 and original index 861197, selection on the full partial prefix of depth 12 and code 110245 returns the complete row with depth 12, base-four code 110245, original node 861197, kind 2, reserved field 0, 1469 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33507", "selected_cut_33507", "Selected cut at depth 13, code 441420, node 862694",
                "At remaining fuel 8 and original index 862694, selection on the full partial prefix of depth 13 and code 441420 returns the complete row with depth 13, base-four code 441420, original node 862694, kind 2, reserved field 0, 2625 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-27561-861213", "unmarked_context_11_27561_861213", "Unmarked parent at depth 11, code 27561",
                "The frontier Boolean is false at remaining fuel 10, original node 861213, the whole prefixCache at depth 11 and code 27561, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-110354-862650", "unmarked_context_12_110354_862650", "Unmarked parent at depth 12, code 110354",
                "The frontier Boolean is false at remaining fuel 9, original node 862650, the whole prefixCache at depth 12 and code 110354, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-27561-861213", "node_context_11_27561_861213", "Original split at fuel 10 and node 861213",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 861179, 861197, 769937, 861212. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-110354-862650", "node_context_12_110354_862650", "Original split at fuel 9 and node 862650",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 862554, 862600, 862643, 862649. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-110245-861197", "context_12_110245_861197", "Context at depth 12, code 110245, node 861197",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 110245 and original node 861197, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-441420-862694", "context_13_441420_862694", "Context at depth 13, code 441420, node 862694",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 441420 and original node 862694, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
