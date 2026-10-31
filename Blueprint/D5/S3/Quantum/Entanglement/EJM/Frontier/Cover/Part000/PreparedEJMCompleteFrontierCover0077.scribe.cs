using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0077Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0077.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0077",
        H("Original frontier context coverage 0077"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03697", "selected_cut_03697", "Selected cut at depth 7, code 7, node 34032",
                "At remaining fuel 14 and original index 34032, selection on the full partial prefix of depth 7 and code 7 returns the complete row with depth 7, base-four code 7, original node 34032, kind 1, reserved field 0, 1 subtree occurrences and completion domain 67108864. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03745", "selected_cut_03745", "Selected cut at depth 14, code 278704, node 118152",
                "At remaining fuel 7 and original index 118152, selection on the full partial prefix of depth 14 and code 278704 returns the complete row with depth 14, base-four code 278704, original node 118152, kind 2, reserved field 0, 261 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-6-1-116312", "unmarked_context_6_1_116312", "Unmarked parent at depth 6, code 1",
                "The frontier Boolean is false at remaining fuel 15, original node 116312, the whole prefixCache at depth 6 and code 1, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-17418-118137", "unmarked_context_12_17418_118137", "Unmarked parent at depth 12, code 17418",
                "The frontier Boolean is false at remaining fuel 9, original node 118137, the whole prefixCache at depth 12 and code 17418, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-6-1-116312", "node_context_6_1_116312", "Original split at fuel 15 and node 116312",
                "The complete original decoder output is the split at coordinate 6, with value children 0 through 3 respectively at original indices 63749, 86586, 116311, 34032. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-17418-118137", "node_context_12_17418_118137", "Original split at fuel 9 and node 118137",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 117986, 118103, 118128, 118136. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-7-7-34032", "context_7_7_34032", "Context at depth 7, code 7, node 34032",
                "The conclusion is adaptive Accepted at the exact depth 7, full base-four code 7 and original node 34032, hence remaining fuel 14, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-278704-118152", "context_14_278704_118152", "Context at depth 14, code 278704, node 118152",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 278704 and original node 118152, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
