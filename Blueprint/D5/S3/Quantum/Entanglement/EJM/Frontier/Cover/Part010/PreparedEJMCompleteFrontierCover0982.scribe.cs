using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0982Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0982.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0982",
        H("Original frontier context coverage 0982"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47140", "selected_cut_47140", "Selected cut at depth 12, code 372502, node 1318384",
                "At remaining fuel 9 and original index 1318384, selection on the full partial prefix of depth 12 and code 372502 returns the complete row with depth 12, base-four code 372502, original node 1318384, kind 2, reserved field 0, 3465 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47188", "selected_cut_47188", "Selected cut at depth 12, code 372559, node 903806",
                "At remaining fuel 9 and original index 903806, selection on the full partial prefix of depth 12 and code 372559 returns the complete row with depth 12, base-four code 372559, original node 903806, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93125-1318385", "unmarked_context_11_93125_1318385", "Unmarked parent at depth 11, code 93125",
                "The frontier Boolean is false at remaining fuel 10, original node 1318385, the whole prefixCache at depth 11 and code 93125, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-93138-1320154", "unmarked_context_11_93138_1320154", "Unmarked parent at depth 11, code 93138",
                "The frontier Boolean is false at remaining fuel 10, original node 1320154, the whole prefixCache at depth 11 and code 93138, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93125-1318385", "node_context_11_93125_1318385", "Original split at fuel 10 and node 1318385",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1318310, 1172003, 1318384, 692794. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-93138-1320154", "node_context_11_93138_1320154", "Original split at fuel 10 and node 1320154",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1320068, 1320097, 1320125, 1320153. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-372502-1318384", "context_12_372502_1318384", "Context at depth 12, code 372502, node 1318384",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 372502 and original node 1318384, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-372559-903806", "context_12_372559_903806", "Context at depth 12, code 372559, node 903806",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 372559 and original node 903806, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
