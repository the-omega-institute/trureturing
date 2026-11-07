using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0215Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0215.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0215",
        H("Original frontier context coverage 0215"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10323", "selected_cut_10323", "Selected cut at depth 12, code 24960, node 281106",
                "At remaining fuel 9 and original index 281106, selection on the full partial prefix of depth 12 and code 24960 returns the complete row with depth 12, base-four code 24960, original node 281106, kind 2, reserved field 0, 1397 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10370", "selected_cut_10370", "Selected cut at depth 12, code 25007, node 282331",
                "At remaining fuel 9 and original index 282331, selection on the full partial prefix of depth 12 and code 25007 returns the complete row with depth 12, base-four code 25007, original node 282331, kind 2, reserved field 0, 1553 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-1559-281035", "unmarked_context_10_1559_281035", "Unmarked parent at depth 10, code 1559",
                "The frontier Boolean is false at remaining fuel 11, original node 281035, the whole prefixCache at depth 10 and code 1559, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6251-282332", "unmarked_context_11_6251_282332", "Unmarked parent at depth 11, code 6251",
                "The frontier Boolean is false at remaining fuel 10, original node 282332, the whole prefixCache at depth 11 and code 6251, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-1559-281035", "node_context_10_1559_281035", "Original split at fuel 11 and node 281035",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 280585, 280688, 280868, 281034. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6251-282332", "node_context_11_6251_282332", "Original split at fuel 10 and node 282332",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 282278, 282296, 282316, 282331. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-1559-281035", "context_10_1559_281035", "Context at depth 10, code 1559, node 281035",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1559 and original node 281035, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_6236_280585, context_11_6237_280688, context_11_6238_280868, context_11_6239_281034.", DescribeRole.Theorem),
            Node("context-11-6251-282332", "context_11_6251_282332", "Context at depth 11, code 6251, node 282332",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6251 and original node 282332, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_25004_282278, context_12_25005_282296, context_12_25006_282316, context_12_25007_282331.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
