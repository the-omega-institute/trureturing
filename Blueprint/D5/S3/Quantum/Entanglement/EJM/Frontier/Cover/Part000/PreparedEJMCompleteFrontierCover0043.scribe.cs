using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0043Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0043.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0043",
        H("Original frontier context coverage 0043"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02066", "selected_cut_02066", "Selected cut at depth 12, code 5459, node 893",
                "At remaining fuel 9 and original index 893, selection on the full partial prefix of depth 12 and code 5459 returns the complete row with depth 12, base-four code 5459, original node 893, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02113", "selected_cut_02113", "Selected cut at depth 12, code 5515, node 69620",
                "At remaining fuel 9 and original index 69620, selection on the full partial prefix of depth 12 and code 5515 returns the complete row with depth 12, base-four code 5515, original node 69620, kind 2, reserved field 0, 2877 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-1364-68179", "unmarked_context_11_1364_68179", "Unmarked parent at depth 11, code 1364",
                "The frontier Boolean is false at remaining fuel 10, original node 68179, the whole prefixCache at depth 11 and code 1364, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1378-69621", "unmarked_context_11_1378_69621", "Unmarked parent at depth 11, code 1378",
                "The frontier Boolean is false at remaining fuel 10, original node 69621, the whole prefixCache at depth 11 and code 1378, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-1364-68179", "node_context_11_1364_68179", "Original split at fuel 10 and node 68179",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1738, 68105, 68178, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1378-69621", "node_context_11_1378_69621", "Original split at fuel 10 and node 69621",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 69420, 69485, 69547, 69620. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-5459-893", "context_12_5459_893", "Context at depth 12, code 5459, node 893",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 5459 and original node 893, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-1378-69621", "context_11_1378_69621", "Context at depth 11, code 1378, node 69621",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 1378 and original node 69621, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_5512_69420, context_12_5513_69485, context_12_5514_69547, context_12_5515_69620.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
