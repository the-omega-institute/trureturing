using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0631Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0631.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0631",
        H("Original frontier context coverage 0631"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30291", "selected_cut_30291", "Selected cut at depth 13, code 417876, node 764755",
                "At remaining fuel 8 and original index 764755, selection on the full partial prefix of depth 13 and code 417876 returns the complete row with depth 13, base-four code 417876, original node 764755, kind 2, reserved field 0, 1273 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30338", "selected_cut_30338", "Selected cut at depth 13, code 417926, node 765788",
                "At remaining fuel 8 and original index 765788, selection on the full partial prefix of depth 13 and code 417926 returns the complete row with depth 13, base-four code 417926, original node 765788, kind 2, reserved field 0, 857 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-104468-764734", "unmarked_context_12_104468_764734", "Unmarked parent at depth 12, code 104468",
                "The frontier Boolean is false at remaining fuel 9, original node 764734, the whole prefixCache at depth 12 and code 104468, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6529-765705", "unmarked_context_10_6529_765705", "Unmarked parent at depth 10, code 6529",
                "The frontier Boolean is false at remaining fuel 11, original node 765705, the whole prefixCache at depth 10 and code 6529, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-104468-764734", "node_context_12_104468_764734", "Original split at fuel 9 and node 764734",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 764670, 764702, 764725, 764733. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6529-765705", "node_context_10_6529_765705", "Original split at fuel 11 and node 765705",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 764652, 765049, 765368, 765704. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-104468-764734", "context_12_104468_764734", "Context at depth 12, code 104468, node 764734",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 104468 and original node 764734, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_417872_764670, context_13_417873_764702, context_13_417874_764725, context_13_417875_764733.", DescribeRole.Theorem),
            Node("context-13-417926-765788", "context_13_417926_765788", "Context at depth 13, code 417926, node 765788",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 417926 and original node 765788, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
