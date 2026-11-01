using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0781Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0781.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0781",
        H("Original frontier context coverage 0781"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37492", "selected_cut_37492", "Selected cut at depth 12, code 299839, node 429285",
                "At remaining fuel 9 and original index 429285, selection on the full partial prefix of depth 12 and code 299839 returns the complete row with depth 12, base-four code 299839, original node 429285, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37538", "selected_cut_37538", "Selected cut at depth 12, code 299903, node 429285",
                "At remaining fuel 9 and original index 429285, selection on the full partial prefix of depth 12 and code 299903 returns the complete row with depth 12, base-four code 299903, original node 429285, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-74959-1002725", "unmarked_context_11_74959_1002725", "Unmarked parent at depth 11, code 74959",
                "The frontier Boolean is false at remaining fuel 10, original node 1002725, the whole prefixCache at depth 11 and code 74959, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18743-1004071", "unmarked_context_10_18743_1004071", "Unmarked parent at depth 10, code 18743",
                "The frontier Boolean is false at remaining fuel 11, original node 1004071, the whole prefixCache at depth 10 and code 18743, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-74959-1002725", "node_context_11_74959_1002725", "Original split at fuel 10 and node 1002725",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1002615, 1002671, 1002724, 429285. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18743-1004071", "node_context_10_18743_1004071", "Original split at fuel 11 and node 1004071",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1003747, 1003850, 1003964, 1004070. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-299839-429285", "context_12_299839_429285", "Context at depth 12, code 299839, node 429285",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 299839 and original node 429285, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-18743-1004071", "context_10_18743_1004071", "Context at depth 10, code 18743, node 1004071",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 18743 and original node 1004071, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_74972_1003747, context_11_74973_1003850, context_11_74974_1003964, context_11_74975_1004070.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
