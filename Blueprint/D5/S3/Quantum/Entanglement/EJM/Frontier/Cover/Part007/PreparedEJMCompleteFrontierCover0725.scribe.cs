using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0725Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0725.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0725",
        H("Original frontier context coverage 0725"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34802", "selected_cut_34802", "Selected cut at depth 10, code 17675, node 908882",
                "At remaining fuel 11 and original index 908882, selection on the full partial prefix of depth 10 and code 17675 returns the complete row with depth 10, base-four code 17675, original node 908882, kind 2, reserved field 0, 429 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34849", "selected_cut_34849", "Selected cut at depth 12, code 282955, node 910664",
                "At remaining fuel 9 and original index 910664, selection on the full partial prefix of depth 12 and code 282955 returns the complete row with depth 12, base-four code 282955, original node 910664, kind 2, reserved field 0, 1825 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-4418-908883", "unmarked_context_9_4418_908883", "Unmarked parent at depth 9, code 4418",
                "The frontier Boolean is false at remaining fuel 12, original node 908883, the whole prefixCache at depth 9 and code 4418, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-70738-910665", "unmarked_context_11_70738_910665", "Unmarked parent at depth 11, code 70738",
                "The frontier Boolean is false at remaining fuel 10, original node 910665, the whole prefixCache at depth 11 and code 70738, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-4418-908883", "node_context_9_4418_908883", "Original split at fuel 12 and node 908883",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 908551, 908774, 908861, 908882. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-70738-910665", "node_context_11_70738_910665", "Original split at fuel 10 and node 910665",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 910601, 896706, 910631, 910664. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-17675-908882", "context_10_17675_908882", "Context at depth 10, code 17675, node 908882",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 17675 and original node 908882, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-70738-910665", "context_11_70738_910665", "Context at depth 11, code 70738, node 910665",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 70738 and original node 910665, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_282952_910601, context_12_282953_896706, context_12_282954_910631, context_12_282955_910664.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
