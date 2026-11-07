using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1093Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1093.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1093",
        H("Original frontier context coverage 1093"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52467", "selected_cut_52467", "Selected cut at depth 10, code 72468, node 1530723",
                "At remaining fuel 11 and original index 1530723, selection on the full partial prefix of depth 10 and code 72468 returns the complete row with depth 10, base-four code 72468, original node 1530723, kind 2, reserved field 0, 2957 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52515", "selected_cut_52515", "Selected cut at depth 11, code 290187, node 1533609",
                "At remaining fuel 10 and original index 1533609, selection on the full partial prefix of depth 11 and code 290187 returns the complete row with depth 11, base-four code 290187, original node 1533609, kind 2, reserved field 0, 1013 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-18116-1530645", "unmarked_context_9_18116_1530645", "Unmarked parent at depth 9, code 18116",
                "The frontier Boolean is false at remaining fuel 12, original node 1530645, the whole prefixCache at depth 9 and code 18116, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-4533-1533353", "unmarked_context_8_4533_1533353", "Unmarked parent at depth 8, code 4533",
                "The frontier Boolean is false at remaining fuel 13, original node 1533353, the whole prefixCache at depth 8 and code 4533, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-18116-1530645", "node_context_9_18116_1530645", "Original split at fuel 12 and node 1530645",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1468246, 1530449, 1530550, 1530644. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-4533-1533353", "node_context_8_4533_1533353", "Original split at fuel 13 and node 1533353",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1532987, 1533230, 1533304, 1533352. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-18116-1530645", "context_9_18116_1530645", "Context at depth 9, code 18116, node 1530645",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 18116 and original node 1530645, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_72464_1468246, context_10_72465_1530449, context_10_72466_1530550, context_10_72467_1530644.", DescribeRole.Theorem),
            Node("context-11-290187-1533609", "context_11_290187_1533609", "Context at depth 11, code 290187, node 1533609",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 290187 and original node 1533609, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
