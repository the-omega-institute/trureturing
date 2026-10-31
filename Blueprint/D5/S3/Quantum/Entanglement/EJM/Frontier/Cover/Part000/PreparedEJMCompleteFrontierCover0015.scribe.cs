using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0015Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0015.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0015",
        H("Original frontier context coverage 0015"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00722", "selected_cut_00722", "Selected cut at depth 13, code 6428, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 6428 returns the complete row with depth 13, base-four code 6428, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00769", "selected_cut_00769", "Selected cut at depth 13, code 6487, node 31005",
                "At remaining fuel 8 and original index 31005, selection on the full partial prefix of depth 13 and code 6487 returns the complete row with depth 13, base-four code 6487, original node 31005, kind 2, reserved field 0, 1449 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-1607-29730", "unmarked_context_12_1607_29730", "Unmarked parent at depth 12, code 1607",
                "The frontier Boolean is false at remaining fuel 9, original node 29730, the whole prefixCache at depth 12 and code 1607, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-1621-31006", "unmarked_context_12_1621_31006", "Unmarked parent at depth 12, code 1621",
                "The frontier Boolean is false at remaining fuel 9, original node 31006, the whole prefixCache at depth 12 and code 1621, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-1607-29730", "node_context_12_1607_29730", "Original split at fuel 9 and node 29730",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 29675, 29713, 29729. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-1621-31006", "node_context_12_1621_31006", "Original split at fuel 9 and node 31006",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 30930, 30978, 31005. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-6428-3444", "context_13_6428_3444", "Context at depth 13, code 6428, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 6428 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-1621-31006", "context_12_1621_31006", "Context at depth 12, code 1621, node 31006",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 1621 and original node 31006, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_6484_3444, context_13_6485_30930, context_13_6486_30978, context_13_6487_31005.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
