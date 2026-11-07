using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0060Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0060.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0060",
        H("Original frontier context coverage 0060"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02882", "selected_cut_02882", "Selected cut at depth 14, code 106640, node 88926",
                "At remaining fuel 7 and original index 88926, selection on the full partial prefix of depth 14 and code 106640 returns the complete row with depth 14, base-four code 106640, original node 88926, kind 2, reserved field 0, 825 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02930", "selected_cut_02930", "Selected cut at depth 13, code 26678, node 90571",
                "At remaining fuel 8 and original index 90571, selection on the full partial prefix of depth 13 and code 26678 returns the complete row with depth 13, base-four code 26678, original node 90571, kind 2, reserved field 0, 2905 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-26660-89010", "unmarked_context_13_26660_89010", "Unmarked parent at depth 13, code 26660",
                "The frontier Boolean is false at remaining fuel 8, original node 89010, the whole prefixCache at depth 13 and code 26660, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-26677-90516", "unmarked_context_13_26677_90516", "Unmarked parent at depth 13, code 26677",
                "The frontier Boolean is false at remaining fuel 8, original node 90516, the whole prefixCache at depth 13 and code 26677, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-26660-89010", "node_context_13_26660_89010", "Original split at fuel 8 and node 89010",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 88926, 88960, 88986, 89009. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-26677-90516", "node_context_13_26677_90516", "Original split at fuel 8 and node 90516",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 90448, 90474, 90497, 90515. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-106640-88926", "context_14_106640_88926", "Context at depth 14, code 106640, node 88926",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 106640 and original node 88926, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-26678-90571", "context_13_26678_90571", "Context at depth 13, code 26678, node 90571",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 26678 and original node 90571, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
