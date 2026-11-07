using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0612Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0612.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0612",
        H("Original frontier context coverage 0612"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29380", "selected_cut_29380", "Selected cut at depth 13, code 373960, node 741755",
                "At remaining fuel 8 and original index 741755, selection on the full partial prefix of depth 13 and code 373960 returns the complete row with depth 13, base-four code 373960, original node 741755, kind 2, reserved field 0, 605 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29426", "selected_cut_29426", "Selected cut at depth 13, code 374018, node 742464",
                "At remaining fuel 8 and original index 742464, selection on the full partial prefix of depth 13 and code 374018 returns the complete row with depth 13, base-four code 374018, original node 742464, kind 2, reserved field 0, 1621 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93489-741745", "unmarked_context_12_93489_741745", "Unmarked parent at depth 12, code 93489",
                "The frontier Boolean is false at remaining fuel 9, original node 741745, the whole prefixCache at depth 12 and code 93489, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1460-742417", "unmarked_context_9_1460_742417", "Unmarked parent at depth 9, code 1460",
                "The frontier Boolean is false at remaining fuel 12, original node 742417, the whole prefixCache at depth 9 and code 1460, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93489-741745", "node_context_12_93489_741745", "Original split at fuel 9 and node 741745",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 741696, 741718, 741736, 741744. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1460-742417", "node_context_9_1460_742417", "Original split at fuel 12 and node 742417",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 739276, 740469, 741617, 742416. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-93489-741745", "context_12_93489_741745", "Context at depth 12, code 93489, node 741745",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93489 and original node 741745, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_373956_741696, context_13_373957_741718, context_13_373958_741736, context_13_373959_741744.", DescribeRole.Theorem),
            Node("context-13-374018-742464", "context_13_374018_742464", "Context at depth 13, code 374018, node 742464",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 374018 and original node 742464, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
