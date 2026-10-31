using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0093Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0093.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0093",
        H("Original frontier context coverage 0093"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04466", "selected_cut_04466", "Selected cut at depth 13, code 73892, node 143262",
                "At remaining fuel 8 and original index 143262, selection on the full partial prefix of depth 13 and code 73892 returns the complete row with depth 13, base-four code 73892, original node 143262, kind 2, reserved field 0, 1833 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04514", "selected_cut_04514", "Selected cut at depth 12, code 18494, node 145361",
                "At remaining fuel 9 and original index 145361, selection on the full partial prefix of depth 12 and code 18494 returns the complete row with depth 12, base-four code 18494, original node 145361, kind 2, reserved field 0, 3333 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-18473-143449", "unmarked_context_12_18473_143449", "Unmarked parent at depth 12, code 18473",
                "The frontier Boolean is false at remaining fuel 9, original node 143449, the whole prefixCache at depth 12 and code 18473, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-4622-145127", "unmarked_context_11_4622_145127", "Unmarked parent at depth 11, code 4622",
                "The frontier Boolean is false at remaining fuel 10, original node 145127, the whole prefixCache at depth 11 and code 4622, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-18473-143449", "node_context_12_18473_143449", "Original split at fuel 9 and node 143449",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 143262, 143390, 143423, 143448. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-4622-145127", "node_context_11_4622_145127", "Original split at fuel 10 and node 145127",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 118489, 144902, 145010, 145126. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-73892-143262", "context_13_73892_143262", "Context at depth 13, code 73892, node 143262",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 73892 and original node 143262, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-18494-145361", "context_12_18494_145361", "Context at depth 12, code 18494, node 145361",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 18494 and original node 145361, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
