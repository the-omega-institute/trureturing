using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0039Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0039.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0039",
        H("Original frontier context coverage 0039"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01875", "selected_cut_01875", "Selected cut at depth 12, code 4779, node 62845",
                "At remaining fuel 9 and original index 62845, selection on the full partial prefix of depth 12 and code 4779 returns the complete row with depth 12, base-four code 4779, original node 62845, kind 2, reserved field 0, 1741 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01921", "selected_cut_01921", "Selected cut at depth 14, code 86050, node 63935",
                "At remaining fuel 7 and original index 63935, selection on the full partial prefix of depth 14 and code 86050 returns the complete row with depth 14, base-four code 86050, original node 63935, kind 2, reserved field 0, 1505 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-1194-62846", "unmarked_context_11_1194_62846", "Unmarked parent at depth 11, code 1194",
                "The frontier Boolean is false at remaining fuel 10, original node 62846, the whole prefixCache at depth 11 and code 1194, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-5377-63853", "unmarked_context_12_5377_63853", "Unmarked parent at depth 12, code 5377",
                "The frontier Boolean is false at remaining fuel 9, original node 63853, the whole prefixCache at depth 12 and code 5377, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-1194-62846", "node_context_11_1194_62846", "Original split at fuel 10 and node 62846",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 62754, 62776, 62823, 62845. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-5377-63853", "node_context_12_5377_63853", "Original split at fuel 9 and node 63853",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 63807, 63834, 63852, 414. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-4779-62845", "context_12_4779_62845", "Context at depth 12, code 4779, node 62845",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 4779 and original node 62845, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-86050-63935", "context_14_86050_63935", "Context at depth 14, code 86050, node 63935",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 86050 and original node 63935, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
