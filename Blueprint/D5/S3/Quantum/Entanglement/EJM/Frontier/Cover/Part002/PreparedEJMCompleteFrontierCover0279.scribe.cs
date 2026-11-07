using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0279Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0279.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0279",
        H("Original frontier context coverage 0279"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13395", "selected_cut_13395", "Selected cut at depth 13, code 106725, node 352009",
                "At remaining fuel 8 and original index 352009, selection on the full partial prefix of depth 13 and code 106725 returns the complete row with depth 13, base-four code 106725, original node 352009, kind 2, reserved field 0, 2073 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13442", "selected_cut_13442", "Selected cut at depth 13, code 106781, node 352969",
                "At remaining fuel 8 and original index 352969, selection on the full partial prefix of depth 13 and code 106781 returns the complete row with depth 13, base-four code 106781, original node 352969, kind 2, reserved field 0, 2649 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26681-352031", "unmarked_context_12_26681_352031", "Unmarked parent at depth 12, code 26681",
                "The frontier Boolean is false at remaining fuel 9, original node 352031, the whole prefixCache at depth 12 and code 26681, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26694-352931", "unmarked_context_12_26694_352931", "Unmarked parent at depth 12, code 26694",
                "The frontier Boolean is false at remaining fuel 9, original node 352931, the whole prefixCache at depth 12 and code 26694, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26681-352031", "node_context_12_26681_352031", "Original split at fuel 9 and node 352031",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 351984, 352009, 352024, 352030. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26694-352931", "node_context_12_26694_352931", "Original split at fuel 9 and node 352931",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 352901, 352921, 352930. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-106725-352009", "context_13_106725_352009", "Context at depth 13, code 106725, node 352009",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 106725 and original node 352009, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-106781-352969", "context_13_106781_352969", "Context at depth 13, code 106781, node 352969",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 106781 and original node 352969, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
