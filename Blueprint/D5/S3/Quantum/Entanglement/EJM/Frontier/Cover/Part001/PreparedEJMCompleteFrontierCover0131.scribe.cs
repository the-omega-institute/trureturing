using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0131Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0131.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0131",
        H("Original frontier context coverage 0131"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06291", "selected_cut_06291", "Selected cut at depth 10, code 1326, node 188793",
                "At remaining fuel 11 and original index 188793, selection on the full partial prefix of depth 10 and code 1326 returns the complete row with depth 10, base-four code 1326, original node 188793, kind 2, reserved field 0, 4089 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06337", "selected_cut_06337", "Selected cut at depth 12, code 21523, node 893",
                "At remaining fuel 9 and original index 893, selection on the full partial prefix of depth 12 and code 21523 returns the complete row with depth 12, base-four code 21523, original node 893, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-1325-188737", "unmarked_context_10_1325_188737", "Unmarked parent at depth 10, code 1325",
                "The frontier Boolean is false at remaining fuel 11, original node 188737, the whole prefixCache at depth 10 and code 1325, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-21522-190259", "unmarked_context_12_21522_190259", "Unmarked parent at depth 12, code 21522",
                "The frontier Boolean is false at remaining fuel 9, original node 190259, the whole prefixCache at depth 12 and code 21522, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-1325-188737", "node_context_10_1325_188737", "Original split at fuel 11 and node 188737",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 188670, 188693, 188714, 188736. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-21522-190259", "node_context_12_21522_190259", "Original split at fuel 9 and node 190259",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 190207, 190230, 190249, 190258. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-1325-188737", "context_10_1325_188737", "Context at depth 10, code 1325, node 188737",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1325 and original node 188737, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_5300_188670, context_11_5301_188693, context_11_5302_188714, context_11_5303_188736.", DescribeRole.Theorem),
            Node("context-12-21523-893", "context_12_21523_893", "Context at depth 12, code 21523, node 893",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 21523 and original node 893, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
