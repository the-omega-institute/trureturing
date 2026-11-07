using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0153Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0153.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0153",
        H("Original frontier context coverage 0153"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07346", "selected_cut_07346", "Selected cut at depth 14, code 360548, node 213722",
                "At remaining fuel 7 and original index 213722, selection on the full partial prefix of depth 14 and code 360548 returns the complete row with depth 14, base-four code 360548, original node 213722, kind 2, reserved field 0, 1169 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07394", "selected_cut_07394", "Selected cut at depth 13, code 90167, node 214893",
                "At remaining fuel 8 and original index 214893, selection on the full partial prefix of depth 13 and code 90167 returns the complete row with depth 13, base-four code 90167, original node 214893, kind 2, reserved field 0, 1077 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-90137-213773", "unmarked_context_13_90137_213773", "Unmarked parent at depth 13, code 90137",
                "The frontier Boolean is false at remaining fuel 8, original node 213773, the whole prefixCache at depth 13 and code 90137, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22540-214763", "unmarked_context_12_22540_214763", "Unmarked parent at depth 12, code 22540",
                "The frontier Boolean is false at remaining fuel 9, original node 214763, the whole prefixCache at depth 12 and code 22540, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-90137-213773", "node_context_13_90137_213773", "Original split at fuel 8 and node 213773",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 213722, 213742, 213761, 213772. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22540-214763", "node_context_12_22540_214763", "Original split at fuel 9 and node 214763",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 214665, 214733, 214752, 214762. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-360548-213722", "context_14_360548_213722", "Context at depth 14, code 360548, node 213722",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 360548 and original node 213722, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-90167-214893", "context_13_90167_214893", "Context at depth 13, code 90167, node 214893",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 90167 and original node 214893, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
