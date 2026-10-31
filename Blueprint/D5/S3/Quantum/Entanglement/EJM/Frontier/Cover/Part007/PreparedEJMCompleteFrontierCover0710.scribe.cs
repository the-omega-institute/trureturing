using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0710Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0710.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0710",
        H("Original frontier context coverage 0710"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34084", "selected_cut_34084", "Selected cut at depth 13, code 451738, node 880159",
                "At remaining fuel 8 and original index 880159, selection on the full partial prefix of depth 13 and code 451738 returns the complete row with depth 13, base-four code 451738, original node 880159, kind 2, reserved field 0, 753 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34131", "selected_cut_34131", "Selected cut at depth 12, code 112956, node 881315",
                "At remaining fuel 9 and original index 881315, selection on the full partial prefix of depth 12 and code 112956 returns the complete row with depth 12, base-four code 112956, original node 881315, kind 2, reserved field 0, 3789 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-112934-880171", "unmarked_context_12_112934_880171", "Unmarked parent at depth 12, code 112934",
                "The frontier Boolean is false at remaining fuel 9, original node 880171, the whole prefixCache at depth 12 and code 112934, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-28238-881267", "unmarked_context_11_28238_881267", "Unmarked parent at depth 11, code 28238",
                "The frontier Boolean is false at remaining fuel 10, original node 881267, the whole prefixCache at depth 11 and code 28238, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-112934-880171", "node_context_12_112934_880171", "Original split at fuel 9 and node 880171",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 880120, 880142, 880159, 880170. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-28238-881267", "node_context_11_28238_881267", "Original split at fuel 10 and node 881267",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 881117, 881167, 881219, 881266. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-451738-880159", "context_13_451738_880159", "Context at depth 13, code 451738, node 880159",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 451738 and original node 880159, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-112956-881315", "context_12_112956_881315", "Context at depth 12, code 112956, node 881315",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 112956 and original node 881315, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
