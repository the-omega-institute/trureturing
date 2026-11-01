using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0833Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0833.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0833",
        H("Original frontier context coverage 0833"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39986", "selected_cut_39986", "Selected cut at depth 11, code 77120, node 167448",
                "At remaining fuel 10 and original index 167448, selection on the full partial prefix of depth 11 and code 77120 returns the complete row with depth 11, base-four code 77120, original node 167448, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40035", "selected_cut_40035", "Selected cut at depth 12, code 308526, node 1087027",
                "At remaining fuel 9 and original index 1087027, selection on the full partial prefix of depth 12 and code 308526 returns the complete row with depth 12, base-four code 308526, original node 1087027, kind 2, reserved field 0, 3429 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-77121-1085361", "unmarked_context_11_77121_1085361", "Unmarked parent at depth 11, code 77121",
                "The frontier Boolean is false at remaining fuel 10, original node 1085361, the whole prefixCache at depth 11 and code 77121, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-77130-1086872", "unmarked_context_11_77130_1086872", "Unmarked parent at depth 11, code 77130",
                "The frontier Boolean is false at remaining fuel 10, original node 1086872, the whole prefixCache at depth 11 and code 77130, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-77121-1085361", "node_context_11_77121_1085361", "Original split at fuel 10 and node 1085361",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 34034, 891951, 1085310, 1085360. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-77130-1086872", "node_context_11_77130_1086872", "Original split at fuel 10 and node 1086872",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1086751, 1086804, 661671, 1086871. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-77120-167448", "context_11_77120_167448", "Context at depth 11, code 77120, node 167448",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 77120 and original node 167448, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-308526-1087027", "context_12_308526_1087027", "Context at depth 12, code 308526, node 1087027",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 308526 and original node 1087027, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
