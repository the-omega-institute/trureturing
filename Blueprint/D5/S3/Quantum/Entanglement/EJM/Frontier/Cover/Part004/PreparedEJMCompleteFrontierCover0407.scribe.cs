using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0407Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0407.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0407",
        H("Original frontier context coverage 0407"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19540", "selected_cut_19540", "Selected cut at depth 13, code 288976, node 500015",
                "At remaining fuel 8 and original index 500015, selection on the full partial prefix of depth 13 and code 288976 returns the complete row with depth 13, base-four code 288976, original node 500015, kind 2, reserved field 0, 949 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19587", "selected_cut_19587", "Selected cut at depth 13, code 289020, node 501263",
                "At remaining fuel 8 and original index 501263, selection on the full partial prefix of depth 13 and code 289020 returns the complete row with depth 13, base-four code 289020, original node 501263, kind 2, reserved field 0, 73 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72243-499994", "unmarked_context_12_72243_499994", "Unmarked parent at depth 12, code 72243",
                "The frontier Boolean is false at remaining fuel 9, original node 499994, the whole prefixCache at depth 12 and code 72243, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-72254-501260", "unmarked_context_12_72254_501260", "Unmarked parent at depth 12, code 72254",
                "The frontier Boolean is false at remaining fuel 9, original node 501260, the whole prefixCache at depth 12 and code 72254, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72243-499994", "node_context_12_72243_499994", "Original split at fuel 9 and node 499994",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 499922, 499966, 499985, 499993. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-72254-501260", "node_context_12_72254_501260", "Original split at fuel 9 and node 501260",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 501190, 501229, 501249, 501259. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-72243-499994", "context_12_72243_499994", "Context at depth 12, code 72243, node 499994",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 72243 and original node 499994, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_288972_499922, context_13_288973_499966, context_13_288974_499985, context_13_288975_499993.", DescribeRole.Theorem),
            Node("context-13-289020-501263", "context_13_289020_501263", "Context at depth 13, code 289020, node 501263",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 289020 and original node 501263, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
