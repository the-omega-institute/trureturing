using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0675Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0675.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0675",
        H("Original frontier context coverage 0675"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32404", "selected_cut_32404", "Selected cut at depth 13, code 433330, node 832832",
                "At remaining fuel 8 and original index 832832, selection on the full partial prefix of depth 13 and code 433330 returns the complete row with depth 13, base-four code 433330, original node 832832, kind 2, reserved field 0, 869 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32450", "selected_cut_32450", "Selected cut at depth 12, code 108371, node 834530",
                "At remaining fuel 9 and original index 834530, selection on the full partial prefix of depth 12 and code 108371 returns the complete row with depth 12, base-four code 108371, original node 834530, kind 2, reserved field 0, 2885 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-108332-832845", "unmarked_context_12_108332_832845", "Unmarked parent at depth 12, code 108332",
                "The frontier Boolean is false at remaining fuel 9, original node 832845, the whole prefixCache at depth 12 and code 108332, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-27092-834531", "unmarked_context_11_27092_834531", "Unmarked parent at depth 11, code 27092",
                "The frontier Boolean is false at remaining fuel 10, original node 834531, the whole prefixCache at depth 11 and code 27092, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-108332-832845", "node_context_12_108332_832845", "Original split at fuel 9 and node 832845",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 832773, 832815, 832832, 832844. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-27092-834531", "node_context_11_27092_834531", "Original split at fuel 10 and node 834531",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 834327, 834379, 834465, 834530. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-433330-832832", "context_13_433330_832832", "Context at depth 13, code 433330, node 832832",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 433330 and original node 832832, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-27092-834531", "context_11_27092_834531", "Context at depth 11, code 27092, node 834531",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 27092 and original node 834531, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_108368_834327, context_12_108369_834379, context_12_108370_834465, context_12_108371_834530.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
