using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1025Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1025.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1025",
        H("Original frontier context coverage 1025"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49203", "selected_cut_49203", "Selected cut at depth 10, code 25413, node 893098",
                "At remaining fuel 11 and original index 893098, selection on the full partial prefix of depth 10 and code 25413 returns the complete row with depth 10, base-four code 25413, original node 893098, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49251", "selected_cut_49251", "Selected cut at depth 12, code 406830, node 1392335",
                "At remaining fuel 9 and original index 1392335, selection on the full partial prefix of depth 12 and code 406830 returns the complete row with depth 12, base-four code 406830, original node 1392335, kind 2, reserved field 0, 2209 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-25412-1390487", "unmarked_context_10_25412_1390487", "Unmarked parent at depth 10, code 25412",
                "The frontier Boolean is false at remaining fuel 11, original node 1390487, the whole prefixCache at depth 10 and code 25412, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-101704-1392128", "unmarked_context_11_101704_1392128", "Unmarked parent at depth 11, code 101704",
                "The frontier Boolean is false at remaining fuel 10, original node 1392128, the whole prefixCache at depth 11 and code 101704, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-25412-1390487", "node_context_10_25412_1390487", "Original split at fuel 11 and node 1390487",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1369428, 1390368, 1390427, 1390486. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-101704-1392128", "node_context_11_101704_1392128", "Original split at fuel 10 and node 1392128",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1392019, 1392085, 1392127. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-25412-1390487", "context_10_25412_1390487", "Context at depth 10, code 25412, node 1390487",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 25412 and original node 1390487, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_101648_1369428, context_11_101649_1390368, context_11_101650_1390427, context_11_101651_1390486.", DescribeRole.Theorem),
            Node("context-12-406830-1392335", "context_12_406830_1392335", "Context at depth 12, code 406830, node 1392335",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 406830 and original node 1392335, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
