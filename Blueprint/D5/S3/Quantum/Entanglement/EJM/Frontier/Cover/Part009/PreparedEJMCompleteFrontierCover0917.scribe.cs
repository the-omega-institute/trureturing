using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0917Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0917.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0917",
        H("Original frontier context coverage 0917"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44020", "selected_cut_44020", "Selected cut at depth 12, code 353071, node 903806",
                "At remaining fuel 9 and original index 903806, selection on the full partial prefix of depth 12 and code 353071 returns the complete row with depth 12, base-four code 353071, original node 903806, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44067", "selected_cut_44067", "Selected cut at depth 11, code 88287, node 1209510",
                "At remaining fuel 10 and original index 1209510, selection on the full partial prefix of depth 11 and code 88287 returns the complete row with depth 11, base-four code 88287, original node 1209510, kind 2, reserved field 0, 1293 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88267-1208273", "unmarked_context_11_88267_1208273", "Unmarked parent at depth 11, code 88267",
                "The frontier Boolean is false at remaining fuel 10, original node 1208273, the whole prefixCache at depth 11 and code 88267, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88286-1209483", "unmarked_context_11_88286_1209483", "Unmarked parent at depth 11, code 88286",
                "The frontier Boolean is false at remaining fuel 10, original node 1209483, the whole prefixCache at depth 11 and code 88286, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88267-1208273", "node_context_11_88267_1208273", "Original split at fuel 10 and node 1208273",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1208188, 1208225, 1208272, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88286-1209483", "node_context_11_88286_1209483", "Original split at fuel 10 and node 1209483",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1209436, 896706, 1209461, 1209482. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-353071-903806", "context_12_353071_903806", "Context at depth 12, code 353071, node 903806",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 353071 and original node 903806, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-88287-1209510", "context_11_88287_1209510", "Context at depth 11, code 88287, node 1209510",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88287 and original node 1209510, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
