using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0922Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0922.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0922",
        H("Original frontier context coverage 0922"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44258", "selected_cut_44258", "Selected cut at depth 11, code 88400, node 1215923",
                "At remaining fuel 10 and original index 1215923, selection on the full partial prefix of depth 11 and code 88400 returns the complete row with depth 11, base-four code 88400, original node 1215923, kind 2, reserved field 0, 5 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44306", "selected_cut_44306", "Selected cut at depth 12, code 353816, node 1218396",
                "At remaining fuel 9 and original index 1218396, selection on the full partial prefix of depth 12 and code 353816 returns the complete row with depth 12, base-four code 353816, original node 1218396, kind 2, reserved field 0, 2605 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-22100-1216266", "unmarked_context_10_22100_1216266", "Unmarked parent at depth 10, code 22100",
                "The frontier Boolean is false at remaining fuel 11, original node 1216266, the whole prefixCache at depth 10 and code 22100, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88452-1218342", "unmarked_context_11_88452_1218342", "Unmarked parent at depth 11, code 88452",
                "The frontier Boolean is false at remaining fuel 10, original node 1218342, the whole prefixCache at depth 11 and code 88452, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-22100-1216266", "node_context_10_22100_1216266", "Original split at fuel 11 and node 1216266",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1215923, 1216062, 1216155, 1216265. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88452-1218342", "node_context_11_88452_1218342", "Original split at fuel 10 and node 1218342",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435160, 1218244, 1218284, 1218341. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-88400-1215923", "context_11_88400_1215923", "Context at depth 11, code 88400, node 1215923",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88400 and original node 1215923, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-353816-1218396", "context_12_353816_1218396", "Context at depth 12, code 353816, node 1218396",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 353816 and original node 1218396, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
