using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0819Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0819.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0819",
        H("Original frontier context coverage 0819"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39315", "selected_cut_39315", "Selected cut at depth 12, code 302868, node 1066053",
                "At remaining fuel 9 and original index 1066053, selection on the full partial prefix of depth 12 and code 302868 returns the complete row with depth 12, base-four code 302868, original node 1066053, kind 2, reserved field 0, 3533 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39362", "selected_cut_39362", "Selected cut at depth 12, code 302912, node 1051681",
                "At remaining fuel 9 and original index 1051681, selection on the full partial prefix of depth 12 and code 302912 returns the complete row with depth 12, base-four code 302912, original node 1051681, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75717-1066163", "unmarked_context_11_75717_1066163", "Unmarked parent at depth 11, code 75717",
                "The frontier Boolean is false at remaining fuel 10, original node 1066163, the whole prefixCache at depth 11 and code 75717, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-4732-1067994", "unmarked_context_9_4732_1067994", "Unmarked parent at depth 9, code 4732",
                "The frontier Boolean is false at remaining fuel 12, original node 1067994, the whole prefixCache at depth 9 and code 4732, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75717-1066163", "node_context_11_75717_1066163", "Original split at fuel 10 and node 1066163",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1066053, 692794, 1066108, 1066162. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-4732-1067994", "node_context_9_4732_1067994", "Original split at fuel 12 and node 1067994",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1065750, 1066628, 1067418, 1067993. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-302868-1066053", "context_12_302868_1066053", "Context at depth 12, code 302868, node 1066053",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 302868 and original node 1066053, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-302912-1051681", "context_12_302912_1051681", "Context at depth 12, code 302912, node 1051681",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 302912 and original node 1051681, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
