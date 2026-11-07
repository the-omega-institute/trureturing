using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0430Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0430.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0430",
        H("Original frontier context coverage 0430"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20643", "selected_cut_20643", "Selected cut at depth 13, code 296301, node 528683",
                "At remaining fuel 8 and original index 528683, selection on the full partial prefix of depth 13 and code 296301 returns the complete row with depth 13, base-four code 296301, original node 528683, kind 2, reserved field 0, 1605 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20690", "selected_cut_20690", "Selected cut at depth 12, code 74111, node 530057",
                "At remaining fuel 9 and original index 530057, selection on the full partial prefix of depth 12 and code 74111 returns the complete row with depth 12, base-four code 74111, original node 530057, kind 2, reserved field 0, 3369 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-74075-528707", "unmarked_context_12_74075_528707", "Unmarked parent at depth 12, code 74075",
                "The frontier Boolean is false at remaining fuel 9, original node 528707, the whole prefixCache at depth 12 and code 74075, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18527-530058", "unmarked_context_11_18527_530058", "Unmarked parent at depth 11, code 18527",
                "The frontier Boolean is false at remaining fuel 10, original node 530058, the whole prefixCache at depth 11 and code 18527, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-74075-528707", "node_context_12_74075_528707", "Original split at fuel 9 and node 528707",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 528683, 528699, 528706. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18527-530058", "node_context_11_18527_530058", "Original split at fuel 10 and node 530058",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 529963, 529988, 530014, 530057. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-296301-528683", "context_13_296301_528683", "Context at depth 13, code 296301, node 528683",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 296301 and original node 528683, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-18527-530058", "context_11_18527_530058", "Context at depth 11, code 18527, node 530058",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18527 and original node 530058, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_74108_529963, context_12_74109_529988, context_12_74110_530014, context_12_74111_530057.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
