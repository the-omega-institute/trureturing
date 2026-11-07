using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0544Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0544.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0544",
        H("Original frontier context coverage 0544"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26115", "selected_cut_26115", "Selected cut at depth 13, code 354432, node 661162",
                "At remaining fuel 8 and original index 661162, selection on the full partial prefix of depth 13 and code 354432 returns the complete row with depth 13, base-four code 354432, original node 661162, kind 2, reserved field 0, 1061 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26162", "selected_cut_26162", "Selected cut at depth 13, code 354497, node 661988",
                "At remaining fuel 8 and original index 661988, selection on the full partial prefix of depth 13 and code 354497 returns the complete row with depth 13, base-four code 354497, original node 661988, kind 2, reserved field 0, 1993 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-5537-661150", "unmarked_context_10_5537_661150", "Unmarked parent at depth 10, code 5537",
                "The frontier Boolean is false at remaining fuel 11, original node 661150, the whole prefixCache at depth 10 and code 5537, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-5538-661945", "unmarked_context_10_5538_661945", "Unmarked parent at depth 10, code 5538",
                "The frontier Boolean is false at remaining fuel 11, original node 661945, the whole prefixCache at depth 10 and code 5538, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-5537-661150", "node_context_10_5537_661150", "Original split at fuel 11 and node 661150",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 660087, 660488, 660741, 661149. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-5538-661945", "node_context_10_5538_661945", "Original split at fuel 11 and node 661945",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 661396, 661670, 661673, 661944. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-5537-661150", "context_10_5537_661150", "Context at depth 10, code 5537, node 661150",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 5537 and original node 661150, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_22148_660087, context_11_22149_660488, context_11_22150_660741, context_11_22151_661149.", DescribeRole.Theorem),
            Node("context-13-354497-661988", "context_13_354497_661988", "Context at depth 13, code 354497, node 661988",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 354497 and original node 661988, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
