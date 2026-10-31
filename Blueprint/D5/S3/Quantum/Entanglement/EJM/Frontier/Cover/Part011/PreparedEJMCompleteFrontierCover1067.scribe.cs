using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1067Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1067.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1067",
        H("Original frontier context coverage 1067"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51218", "selected_cut_51218", "Selected cut at depth 11, code 279173, node 1468419",
                "At remaining fuel 10 and original index 1468419, selection on the full partial prefix of depth 11 and code 279173 returns the complete row with depth 11, base-four code 279173, original node 1468419, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51264", "selected_cut_51264", "Selected cut at depth 6, code 273, node 1475984",
                "At remaining fuel 15 and original index 1475984, selection on the full partial prefix of depth 6 and code 273 returns the complete row with depth 6, base-four code 273, original node 1475984, kind 1, reserved field 0, 1 subtree occurrences and completion domain 268435456. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-69793-1473999", "unmarked_context_10_69793_1473999", "Unmarked parent at depth 10, code 69793",
                "The frontier Boolean is false at remaining fuel 11, original node 1473999, the whole prefixCache at depth 10 and code 69793, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-6-272-1475983", "unmarked_context_6_272_1475983", "Unmarked parent at depth 6, code 272",
                "The frontier Boolean is false at remaining fuel 15, original node 1475983, the whole prefixCache at depth 6 and code 272, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-69793-1473999", "node_context_10_69793_1473999", "Original split at fuel 11 and node 1473999",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1473784, 1468419, 1473885, 1473998. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-6-272-1475983", "node_context_6_272_1475983", "Original split at fuel 15 and node 1475983",
                "The complete original decoder output is the split at coordinate 6, with value children 0 through 3 respectively at original indices 1471522, 1473588, 1475982, 34032. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-279173-1468419", "context_11_279173_1468419", "Context at depth 11, code 279173, node 1468419",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 279173 and original node 1468419, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-6-273-1475984", "context_6_273_1475984", "Context at depth 6, code 273, node 1475984",
                "The conclusion is adaptive Accepted at the exact depth 6, full base-four code 273 and original node 1475984, hence remaining fuel 15, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
