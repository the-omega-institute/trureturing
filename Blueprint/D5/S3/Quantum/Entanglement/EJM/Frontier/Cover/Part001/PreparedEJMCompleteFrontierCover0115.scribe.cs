using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0115Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0115.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0115",
        H("Original frontier context coverage 0115"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05522", "selected_cut_05522", "Selected cut at depth 13, code 82304, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 82304 returns the complete row with depth 13, base-four code 82304, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05569", "selected_cut_05569", "Selected cut at depth 12, code 20626, node 172174",
                "At remaining fuel 9 and original index 172174, selection on the full partial prefix of depth 12 and code 20626 returns the complete row with depth 12, base-four code 20626, original node 172174, kind 2, reserved field 0, 1753 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-1285-170816", "unmarked_context_10_1285_170816", "Unmarked parent at depth 10, code 1285",
                "The frontier Boolean is false at remaining fuel 11, original node 170816, the whole prefixCache at depth 10 and code 1285, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1288-172073", "unmarked_context_10_1288_172073", "Unmarked parent at depth 10, code 1288",
                "The frontier Boolean is false at remaining fuel 11, original node 172073, the whole prefixCache at depth 10 and code 1288, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-1285-170816", "node_context_10_1285_170816", "Original split at fuel 11 and node 170816",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 170468, 170554, 170815, 1736. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1288-172073", "node_context_10_1288_172073", "Original split at fuel 11 and node 172073",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 171703, 171826, 171957, 172072. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-1285-170816", "context_10_1285_170816", "Context at depth 10, code 1285, node 170816",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1285 and original node 170816, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_5140_170468, context_11_5141_170554, context_11_5142_170815, context_11_5143_1736.", DescribeRole.Theorem),
            Node("context-12-20626-172174", "context_12_20626_172174", "Context at depth 12, code 20626, node 172174",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 20626 and original node 172174, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
