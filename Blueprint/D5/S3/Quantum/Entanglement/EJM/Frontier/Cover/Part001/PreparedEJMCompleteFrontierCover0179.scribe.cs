using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0179Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0179.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0179",
        H("Original frontier context coverage 0179"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08596", "selected_cut_08596", "Selected cut at depth 13, code 92272, node 240801",
                "At remaining fuel 8 and original index 240801, selection on the full partial prefix of depth 13 and code 92272 returns the complete row with depth 13, base-four code 92272, original node 240801, kind 2, reserved field 0, 1565 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08643", "selected_cut_08643", "Selected cut at depth 13, code 92319, node 241908",
                "At remaining fuel 8 and original index 241908, selection on the full partial prefix of depth 13 and code 92319 returns the complete row with depth 13, base-four code 92319, original node 241908, kind 2, reserved field 0, 985 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-23067-240775", "unmarked_context_12_23067_240775", "Unmarked parent at depth 12, code 23067",
                "The frontier Boolean is false at remaining fuel 9, original node 240775, the whole prefixCache at depth 12 and code 23067, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-23078-241816", "unmarked_context_12_23078_241816", "Unmarked parent at depth 12, code 23078",
                "The frontier Boolean is false at remaining fuel 9, original node 241816, the whole prefixCache at depth 12 and code 23078, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-23067-240775", "node_context_12_23067_240775", "Original split at fuel 9 and node 240775",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 240690, 240739, 240763, 240774. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-23078-241816", "node_context_12_23078_241816", "Original split at fuel 9 and node 241816",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 241752, 241791, 241808, 241815. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-23067-240775", "context_12_23067_240775", "Context at depth 12, code 23067, node 240775",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 23067 and original node 240775, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_92268_240690, context_13_92269_240739, context_13_92270_240763, context_13_92271_240774.", DescribeRole.Theorem),
            Node("context-13-92319-241908", "context_13_92319_241908", "Context at depth 13, code 92319, node 241908",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 92319 and original node 241908, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
