using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0405Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0405.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0405",
        H("Original frontier context coverage 0405"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19443", "selected_cut_19443", "Selected cut at depth 13, code 288867, node 497338",
                "At remaining fuel 8 and original index 497338, selection on the full partial prefix of depth 13 and code 288867 returns the complete row with depth 13, base-four code 288867, original node 497338, kind 2, reserved field 0, 1261 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19490", "selected_cut_19490", "Selected cut at depth 13, code 288917, node 498780",
                "At remaining fuel 8 and original index 498780, selection on the full partial prefix of depth 13 and code 288917 returns the complete row with depth 13, base-four code 288917, original node 498780, kind 2, reserved field 0, 2017 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72216-497339", "unmarked_context_12_72216_497339", "Unmarked parent at depth 12, code 72216",
                "The frontier Boolean is false at remaining fuel 9, original node 497339, the whole prefixCache at depth 12 and code 72216, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-72228-498726", "unmarked_context_12_72228_498726", "Unmarked parent at depth 12, code 72228",
                "The frontier Boolean is false at remaining fuel 9, original node 498726, the whole prefixCache at depth 12 and code 72228, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72216-497339", "node_context_12_72216_497339", "Original split at fuel 9 and node 497339",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 497230, 497284, 497311, 497338. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-72228-498726", "node_context_12_72228_498726", "Original split at fuel 9 and node 498726",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 498607, 498672, 498700, 498725. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-288867-497338", "context_13_288867_497338", "Context at depth 13, code 288867, node 497338",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 288867 and original node 497338, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-288917-498780", "context_13_288917_498780", "Context at depth 13, code 288917, node 498780",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 288917 and original node 498780, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
