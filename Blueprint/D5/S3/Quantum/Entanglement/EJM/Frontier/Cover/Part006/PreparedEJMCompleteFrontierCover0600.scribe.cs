using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0600Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0600.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0600",
        H("Original frontier context coverage 0600"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28803", "selected_cut_28803", "Selected cut at depth 12, code 92976, node 726393",
                "At remaining fuel 9 and original index 726393, selection on the full partial prefix of depth 12 and code 92976 returns the complete row with depth 12, base-four code 92976, original node 726393, kind 2, reserved field 0, 4053 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28851", "selected_cut_28851", "Selected cut at depth 12, code 93042, node 728209",
                "At remaining fuel 9 and original index 728209, selection on the full partial prefix of depth 12 and code 93042 returns the complete row with depth 12, base-four code 93042, original node 728209, kind 2, reserved field 0, 1921 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-92977-726466", "unmarked_context_12_92977_726466", "Unmarked parent at depth 12, code 92977",
                "The frontier Boolean is false at remaining fuel 9, original node 726466, the whole prefixCache at depth 12 and code 92977, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-5814-728089", "unmarked_context_10_5814_728089", "Unmarked parent at depth 10, code 5814",
                "The frontier Boolean is false at remaining fuel 11, original node 728089, the whole prefixCache at depth 10 and code 5814, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-92977-726466", "node_context_12_92977_726466", "Original split at fuel 9 and node 726466",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 726406, 726444, 726457, 726465. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-5814-728089", "node_context_10_5814_728089", "Original split at fuel 11 and node 728089",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 727897, 727953, 728036, 728088. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-92976-726393", "context_12_92976_726393", "Context at depth 12, code 92976, node 726393",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 92976 and original node 726393, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-93042-728209", "context_12_93042_728209", "Context at depth 12, code 93042, node 728209",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93042 and original node 728209, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
