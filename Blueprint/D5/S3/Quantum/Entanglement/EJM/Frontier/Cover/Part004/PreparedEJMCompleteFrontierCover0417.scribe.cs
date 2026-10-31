using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0417Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0417.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0417",
        H("Original frontier context coverage 0417"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20020", "selected_cut_20020", "Selected cut at depth 13, code 290029, node 512410",
                "At remaining fuel 8 and original index 512410, selection on the full partial prefix of depth 13 and code 290029 returns the complete row with depth 13, base-four code 290029, original node 512410, kind 2, reserved field 0, 2229 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20067", "selected_cut_20067", "Selected cut at depth 13, code 290094, node 513256",
                "At remaining fuel 8 and original index 513256, selection on the full partial prefix of depth 13 and code 290094 returns the complete row with depth 13, base-four code 290094, original node 513256, kind 2, reserved field 0, 1689 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72507-512439", "unmarked_context_12_72507_512439", "Unmarked parent at depth 12, code 72507",
                "The frontier Boolean is false at remaining fuel 9, original node 512439, the whole prefixCache at depth 12 and code 72507, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-72522-513214", "unmarked_context_12_72522_513214", "Unmarked parent at depth 12, code 72522",
                "The frontier Boolean is false at remaining fuel 9, original node 513214, the whole prefixCache at depth 12 and code 72522, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72507-512439", "node_context_12_72507_512439", "Original split at fuel 9 and node 512439",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 512378, 512410, 512431, 512438. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-72522-513214", "node_context_12_72522_513214", "Original split at fuel 9 and node 513214",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 513184, 513207, 513213. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-290029-512410", "context_13_290029_512410", "Context at depth 13, code 290029, node 512410",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 290029 and original node 512410, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-290094-513256", "context_13_290094_513256", "Context at depth 13, code 290094, node 513256",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 290094 and original node 513256, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
