using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0529Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0529.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0529",
        H("Original frontier context coverage 0529"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25394", "selected_cut_25394", "Selected cut at depth 11, code 21782, node 642478",
                "At remaining fuel 10 and original index 642478, selection on the full partial prefix of depth 11 and code 21782 returns the complete row with depth 11, base-four code 21782, original node 642478, kind 2, reserved field 0, 3633 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25442", "selected_cut_25442", "Selected cut at depth 14, code 1400993, node 643785",
                "At remaining fuel 7 and original index 643785, selection on the full partial prefix of depth 14 and code 1400993 returns the complete row with depth 14, base-four code 1400993, original node 643785, kind 2, reserved field 0, 1597 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-5445-642479", "unmarked_context_10_5445_642479", "Unmarked parent at depth 10, code 5445",
                "The frontier Boolean is false at remaining fuel 11, original node 642479, the whole prefixCache at depth 10 and code 5445, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-21889-643734", "unmarked_context_11_21889_643734", "Unmarked parent at depth 11, code 21889",
                "The frontier Boolean is false at remaining fuel 10, original node 643734, the whole prefixCache at depth 11 and code 21889, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-5445-642479", "node_context_10_5445_642479", "Original split at fuel 11 and node 642479",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 642393, 451541, 642478, 1736. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-21889-643734", "node_context_11_21889_643734", "Original split at fuel 10 and node 643734",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 895, 643425, 643567, 643733. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-21782-642478", "context_11_21782_642478", "Context at depth 11, code 21782, node 642478",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 21782 and original node 642478, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-1400993-643785", "context_14_1400993_643785", "Context at depth 14, code 1400993, node 643785",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 1400993 and original node 643785, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
