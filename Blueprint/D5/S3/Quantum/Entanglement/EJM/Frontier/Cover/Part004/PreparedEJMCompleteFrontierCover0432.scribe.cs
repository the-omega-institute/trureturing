using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0432Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0432.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0432",
        H("Original frontier context coverage 0432"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20739", "selected_cut_20739", "Selected cut at depth 12, code 74160, node 531072",
                "At remaining fuel 9 and original index 531072, selection on the full partial prefix of depth 12 and code 74160 returns the complete row with depth 12, base-four code 74160, original node 531072, kind 2, reserved field 0, 1009 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20785", "selected_cut_20785", "Selected cut at depth 13, code 298063, node 532054",
                "At remaining fuel 8 and original index 532054, selection on the full partial prefix of depth 13 and code 298063 returns the complete row with depth 13, base-four code 298063, original node 532054, kind 2, reserved field 0, 489 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-4634-531059", "unmarked_context_10_4634_531059", "Unmarked parent at depth 10, code 4634",
                "The frontier Boolean is false at remaining fuel 11, original node 531059, the whole prefixCache at depth 10 and code 4634, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18628-532056", "unmarked_context_11_18628_532056", "Unmarked parent at depth 11, code 18628",
                "The frontier Boolean is false at remaining fuel 10, original node 532056, the whole prefixCache at depth 11 and code 18628, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-4634-531059", "node_context_10_4634_531059", "Original split at fuel 11 and node 531059",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 530840, 530926, 530997, 531058. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18628-532056", "node_context_11_18628_532056", "Original split at fuel 10 and node 532056",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435160, 531908, 531980, 532055. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-4634-531059", "context_10_4634_531059", "Context at depth 10, code 4634, node 531059",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 4634 and original node 531059, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_18536_530840, context_11_18537_530926, context_11_18538_530997, context_11_18539_531058.", DescribeRole.Theorem),
            Node("context-11-18628-532056", "context_11_18628_532056", "Context at depth 11, code 18628, node 532056",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18628 and original node 532056, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_74512_435160, context_12_74513_531908, context_12_74514_531980, context_12_74515_532055.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
