using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0905Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0905.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0905",
        H("Original frontier context coverage 0905"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43443", "selected_cut_43443", "Selected cut at depth 11, code 87453, node 1188855",
                "At remaining fuel 10 and original index 1188855, selection on the full partial prefix of depth 11 and code 87453 returns the complete row with depth 11, base-four code 87453, original node 1188855, kind 2, reserved field 0, 1421 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43490", "selected_cut_43490", "Selected cut at depth 12, code 350756, node 1190851",
                "At remaining fuel 9 and original index 1190851, selection on the full partial prefix of depth 12 and code 350756 returns the complete row with depth 12, base-four code 350756, original node 1190851, kind 2, reserved field 0, 2353 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-21863-1188913", "unmarked_context_10_21863_1188913", "Unmarked parent at depth 10, code 21863",
                "The frontier Boolean is false at remaining fuel 11, original node 1188913, the whole prefixCache at depth 10 and code 21863, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-87688-1190804", "unmarked_context_11_87688_1190804", "Unmarked parent at depth 11, code 87688",
                "The frontier Boolean is false at remaining fuel 10, original node 1190804, the whole prefixCache at depth 11 and code 87688, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-21863-1188913", "node_context_10_21863_1188913", "Original split at fuel 11 and node 1188913",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1188803, 1188855, 1188889, 1188912. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-87688-1190804", "node_context_11_87688_1190804", "Original split at fuel 10 and node 1190804",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 355612, 1190684, 1190736, 1190803. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-87453-1188855", "context_11_87453_1188855", "Context at depth 11, code 87453, node 1188855",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 87453 and original node 1188855, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-350756-1190851", "context_12_350756_1190851", "Context at depth 12, code 350756, node 1190851",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 350756 and original node 1190851, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
