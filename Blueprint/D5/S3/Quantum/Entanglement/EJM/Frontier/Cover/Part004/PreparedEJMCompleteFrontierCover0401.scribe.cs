using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0401Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0401.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0401",
        H("Original frontier context coverage 0401"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19251", "selected_cut_19251", "Selected cut at depth 13, code 288225, node 491945",
                "At remaining fuel 8 and original index 491945, selection on the full partial prefix of depth 13 and code 288225 returns the complete row with depth 13, base-four code 288225, original node 491945, kind 2, reserved field 0, 505 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19297", "selected_cut_19297", "Selected cut at depth 12, code 72079, node 492919",
                "At remaining fuel 9 and original index 492919, selection on the full partial prefix of depth 12 and code 72079 returns the complete row with depth 12, base-four code 72079, original node 492919, kind 2, reserved field 0, 2849 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72056-491993", "unmarked_context_12_72056_491993", "Unmarked parent at depth 12, code 72056",
                "The frontier Boolean is false at remaining fuel 9, original node 491993, the whole prefixCache at depth 12 and code 72056, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4504-492921", "unmarked_context_10_4504_492921", "Unmarked parent at depth 10, code 4504",
                "The frontier Boolean is false at remaining fuel 11, original node 492921, the whole prefixCache at depth 10 and code 4504, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72056-491993", "node_context_12_72056_491993", "Original split at fuel 9 and node 491993",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 491945, 491979, 491992. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4504-492921", "node_context_10_4504_492921", "Original split at fuel 11 and node 492921",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 492546, 492714, 492820, 492920. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-288225-491945", "context_13_288225_491945", "Context at depth 13, code 288225, node 491945",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 288225 and original node 491945, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-4504-492921", "context_10_4504_492921", "Context at depth 10, code 4504, node 492921",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 4504 and original node 492921, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_18016_492546, context_11_18017_492714, context_11_18018_492820, context_11_18019_492920.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
