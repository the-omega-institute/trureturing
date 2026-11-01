using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0720Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0720.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0720",
        H("Original frontier context coverage 0720"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34563", "selected_cut_34563", "Selected cut at depth 13, code 1124382, node 898607",
                "At remaining fuel 8 and original index 898607, selection on the full partial prefix of depth 13 and code 1124382 returns the complete row with depth 13, base-four code 1124382, original node 898607, kind 2, reserved field 0, 1157 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34610", "selected_cut_34610", "Selected cut at depth 12, code 281135, node 900806",
                "At remaining fuel 9 and original index 900806, selection on the full partial prefix of depth 12 and code 281135 returns the complete row with depth 12, base-four code 281135, original node 900806, kind 2, reserved field 0, 2985 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-281095-898627", "unmarked_context_12_281095_898627", "Unmarked parent at depth 12, code 281095",
                "The frontier Boolean is false at remaining fuel 9, original node 898627, the whole prefixCache at depth 12 and code 281095, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-70283-900807", "unmarked_context_11_70283_900807", "Unmarked parent at depth 11, code 70283",
                "The frontier Boolean is false at remaining fuel 10, original node 900807, the whole prefixCache at depth 11 and code 70283, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-281095-898627", "node_context_12_281095_898627", "Original split at fuel 9 and node 898627",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 898553, 898578, 898607, 898626. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-70283-900807", "node_context_11_70283_900807", "Original split at fuel 10 and node 900807",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1738, 1738, 900699, 900806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1124382-898607", "context_13_1124382_898607", "Context at depth 13, code 1124382, node 898607",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1124382 and original node 898607, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-70283-900807", "context_11_70283_900807", "Context at depth 11, code 70283, node 900807",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 70283 and original node 900807, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_281132_1738, context_12_281133_1738, context_12_281134_900699, context_12_281135_900806.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
