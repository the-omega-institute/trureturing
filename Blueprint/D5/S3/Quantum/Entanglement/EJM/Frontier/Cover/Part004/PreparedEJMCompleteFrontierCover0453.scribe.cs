using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0453Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0453.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0453",
        H("Original frontier context coverage 0453"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21746", "selected_cut_21746", "Selected cut at depth 13, code 301124, node 556321",
                "At remaining fuel 8 and original index 556321, selection on the full partial prefix of depth 13 and code 301124 returns the complete row with depth 13, base-four code 301124, original node 556321, kind 2, reserved field 0, 1445 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21795", "selected_cut_21795", "Selected cut at depth 13, code 301179, node 557402",
                "At remaining fuel 8 and original index 557402, selection on the full partial prefix of depth 13 and code 301179 returns the complete row with depth 13, base-four code 301179, original node 557402, kind 2, reserved field 0, 813 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75281-556370", "unmarked_context_12_75281_556370", "Unmarked parent at depth 12, code 75281",
                "The frontier Boolean is false at remaining fuel 9, original node 556370, the whole prefixCache at depth 12 and code 75281, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-75293-557331", "unmarked_context_12_75293_557331", "Unmarked parent at depth 12, code 75293",
                "The frontier Boolean is false at remaining fuel 9, original node 557331, the whole prefixCache at depth 12 and code 75293, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75281-556370", "node_context_12_75281_556370", "Original split at fuel 9 and node 556370",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 556321, 556346, 556363, 556369. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-75293-557331", "node_context_12_75293_557331", "Original split at fuel 9 and node 557331",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 557284, 557312, 557325, 557330. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-301124-556321", "context_13_301124_556321", "Context at depth 13, code 301124, node 556321",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 301124 and original node 556321, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-301179-557402", "context_13_301179_557402", "Context at depth 13, code 301179, node 557402",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 301179 and original node 557402, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
