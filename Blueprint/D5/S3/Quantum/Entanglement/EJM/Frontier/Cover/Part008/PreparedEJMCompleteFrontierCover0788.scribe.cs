using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0788Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0788.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0788",
        H("Original frontier context coverage 0788"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37827", "selected_cut_37827", "Selected cut at depth 12, code 300405, node 891951",
                "At remaining fuel 9 and original index 891951, selection on the full partial prefix of depth 12 and code 300405 returns the complete row with depth 12, base-four code 300405, original node 891951, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37874", "selected_cut_37874", "Selected cut at depth 13, code 1202213, node 1015885",
                "At remaining fuel 8 and original index 1015885, selection on the full partial prefix of depth 13 and code 1202213 returns the complete row with depth 13, base-four code 1202213, original node 1015885, kind 2, reserved field 0, 1501 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75101-1014406", "unmarked_context_11_75101_1014406", "Unmarked parent at depth 11, code 75101",
                "The frontier Boolean is false at remaining fuel 10, original node 1014406, the whole prefixCache at depth 11 and code 75101, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75137-1015767", "unmarked_context_11_75137_1015767", "Unmarked parent at depth 11, code 75137",
                "The frontier Boolean is false at remaining fuel 10, original node 1015767, the whole prefixCache at depth 11 and code 75137, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75101-1014406", "node_context_11_75101_1014406", "Original split at fuel 10 and node 1014406",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1014369, 891951, 1014388, 1014405. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75137-1015767", "node_context_11_75137_1015767", "Original split at fuel 10 and node 1015767",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1015528, 1015611, 1015684, 1015766. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-300405-891951", "context_12_300405_891951", "Context at depth 12, code 300405, node 891951",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 300405 and original node 891951, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-1202213-1015885", "context_13_1202213_1015885", "Context at depth 13, code 1202213, node 1015885",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1202213 and original node 1015885, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
