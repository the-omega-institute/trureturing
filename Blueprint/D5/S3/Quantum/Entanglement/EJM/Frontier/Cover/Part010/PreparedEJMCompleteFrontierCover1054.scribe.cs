using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1054Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1054.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1054",
        H("Original frontier context coverage 1054"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50597", "selected_cut_50597", "Selected cut at depth 11, code 106445, node 1447277",
                "At remaining fuel 10 and original index 1447277, selection on the full partial prefix of depth 11 and code 106445 returns the complete row with depth 11, base-four code 106445, original node 1447277, kind 2, reserved field 0, 2657 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50643", "selected_cut_50643", "Selected cut at depth 12, code 440355, node 1449026",
                "At remaining fuel 9 and original index 1449026, selection on the full partial prefix of depth 12 and code 440355 returns the complete row with depth 12, base-four code 440355, original node 1449026, kind 2, reserved field 0, 1605 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-106444-1447209", "unmarked_context_11_106444_1447209", "Unmarked parent at depth 11, code 106444",
                "The frontier Boolean is false at remaining fuel 10, original node 1447209, the whole prefixCache at depth 11 and code 106444, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-27521-1448896", "unmarked_context_10_27521_1448896", "Unmarked parent at depth 10, code 27521",
                "The frontier Boolean is false at remaining fuel 11, original node 1448896, the whole prefixCache at depth 10 and code 27521, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-106444-1447209", "node_context_11_106444_1447209", "Original split at fuel 10 and node 1447209",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1416143, 1447138, 1447176, 1447208. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-27521-1448896", "node_context_10_27521_1448896", "Original split at fuel 11 and node 1448896",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1448700, 1192826, 1448792, 1448895. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-106444-1447209", "context_11_106444_1447209", "Context at depth 11, code 106444, node 1447209",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 106444 and original node 1447209, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_425776_1416143, context_12_425777_1447138, context_12_425778_1447176, context_12_425779_1447208.", DescribeRole.Theorem),
            Node("context-12-440355-1449026", "context_12_440355_1449026", "Context at depth 12, code 440355, node 1449026",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 440355 and original node 1449026, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
