using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0657Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0657.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0657",
        H("Original frontier context coverage 0657"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31540", "selected_cut_31540", "Selected cut at depth 13, code 424153, node 809515",
                "At remaining fuel 8 and original index 809515, selection on the full partial prefix of depth 13 and code 424153 returns the complete row with depth 13, base-four code 424153, original node 809515, kind 2, reserved field 0, 2733 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31587", "selected_cut_31587", "Selected cut at depth 13, code 424218, node 810423",
                "At remaining fuel 8 and original index 810423, selection on the full partial prefix of depth 13 and code 424218 returns the complete row with depth 13, base-four code 424218, original node 810423, kind 2, reserved field 0, 1421 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-106038-809540", "unmarked_context_12_106038_809540", "Unmarked parent at depth 12, code 106038",
                "The frontier Boolean is false at remaining fuel 9, original node 809540, the whole prefixCache at depth 12 and code 106038, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-106053-810364", "unmarked_context_12_106053_810364", "Unmarked parent at depth 12, code 106053",
                "The frontier Boolean is false at remaining fuel 9, original node 810364, the whole prefixCache at depth 12 and code 106053, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-106038-809540", "node_context_12_106038_809540", "Original split at fuel 9 and node 809540",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 809480, 809515, 809533, 809539. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-106053-810364", "node_context_12_106053_810364", "Original split at fuel 9 and node 810364",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 810337, 810357, 810363. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-424153-809515", "context_13_424153_809515", "Context at depth 13, code 424153, node 809515",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 424153 and original node 809515, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-424218-810423", "context_13_424218_810423", "Context at depth 13, code 424218, node 810423",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 424218 and original node 810423, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
