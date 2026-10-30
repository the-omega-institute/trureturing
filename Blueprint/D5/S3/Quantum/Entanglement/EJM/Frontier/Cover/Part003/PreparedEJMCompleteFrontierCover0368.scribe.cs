using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0368Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0368.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0368",
        H("Original frontier context coverage 0368"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17666", "selected_cut_17666", "Selected cut at depth 13, code 282764, node 450143",
                "At remaining fuel 8 and original index 450143, selection on the full partial prefix of depth 13 and code 282764 returns the complete row with depth 13, base-four code 282764, original node 450143, kind 2, reserved field 0, 785 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17712", "selected_cut_17712", "Selected cut at depth 10, code 4419, node 3440",
                "At remaining fuel 11 and original index 3440, selection on the full partial prefix of depth 10 and code 4419 returns the complete row with depth 10, base-four code 4419, original node 3440, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-70691-450194", "unmarked_context_12_70691_450194", "Unmarked parent at depth 12, code 70691",
                "The frontier Boolean is false at remaining fuel 9, original node 450194, the whole prefixCache at depth 12 and code 70691, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1104-450981", "unmarked_context_9_1104_450981", "Unmarked parent at depth 9, code 1104",
                "The frontier Boolean is false at remaining fuel 12, original node 450981, the whole prefixCache at depth 9 and code 1104, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-70691-450194", "node_context_12_70691_450194", "Original split at fuel 9 and node 450194",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 450143, 450168, 450188, 450193. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1104-450981", "node_context_9_1104_450981", "Original split at fuel 12 and node 450981",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 449392, 449977, 450980, 3440. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-282764-450143", "context_13_282764_450143", "Context at depth 13, code 282764, node 450143",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 282764 and original node 450143, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-1104-450981", "context_9_1104_450981", "Context at depth 9, code 1104, node 450981",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 1104 and original node 450981, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_4416_449392, context_10_4417_449977, context_10_4418_450980, context_10_4419_3440.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
