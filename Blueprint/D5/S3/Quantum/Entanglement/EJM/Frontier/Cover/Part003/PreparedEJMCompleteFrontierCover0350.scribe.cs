using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0350Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0350.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0350",
        H("Original frontier context coverage 0350"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16804", "selected_cut_16804", "Selected cut at depth 13, code 113845, node 427820",
                "At remaining fuel 8 and original index 427820, selection on the full partial prefix of depth 13 and code 113845 returns the complete row with depth 13, base-four code 113845, original node 427820, kind 2, reserved field 0, 2249 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16851", "selected_cut_16851", "Selected cut at depth 13, code 113889, node 428705",
                "At remaining fuel 8 and original index 428705, selection on the full partial prefix of depth 13 and code 113889 returns the complete row with depth 13, base-four code 113889, original node 428705, kind 2, reserved field 0, 2993 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-28461-427852", "unmarked_context_12_28461_427852", "Unmarked parent at depth 12, code 28461",
                "The frontier Boolean is false at remaining fuel 9, original node 427852, the whole prefixCache at depth 12 and code 28461, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-7117-428655", "unmarked_context_11_7117_428655", "Unmarked parent at depth 11, code 7117",
                "The frontier Boolean is false at remaining fuel 10, original node 428655, the whole prefixCache at depth 11 and code 7117, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-28461-427852", "node_context_12_28461_427852", "Original split at fuel 9 and node 427852",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 427787, 427820, 427844, 427851. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-7117-428655", "node_context_11_7117_428655", "Original split at fuel 10 and node 428655",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 428450, 428514, 428582, 428654. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-113845-427820", "context_13_113845_427820", "Context at depth 13, code 113845, node 427820",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 113845 and original node 427820, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-113889-428705", "context_13_113889_428705", "Context at depth 13, code 113889, node 428705",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 113889 and original node 428705, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
