using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0142Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0142.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0142",
        H("Original frontier context coverage 0142"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06819", "selected_cut_06819", "Selected cut at depth 13, code 88080, node 201874",
                "At remaining fuel 8 and original index 201874, selection on the full partial prefix of depth 13 and code 88080 returns the complete row with depth 13, base-four code 88080, original node 201874, kind 2, reserved field 0, 2905 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06865", "selected_cut_06865", "Selected cut at depth 13, code 88111, node 203269",
                "At remaining fuel 8 and original index 203269, selection on the full partial prefix of depth 13 and code 88111 returns the complete row with depth 13, base-four code 88111, original node 203269, kind 2, reserved field 0, 1053 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22019-201820", "unmarked_context_12_22019_201820", "Unmarked parent at depth 12, code 22019",
                "The frontier Boolean is false at remaining fuel 9, original node 201820, the whole prefixCache at depth 12 and code 22019, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5506-203271", "unmarked_context_11_5506_203271", "Unmarked parent at depth 11, code 5506",
                "The frontier Boolean is false at remaining fuel 10, original node 203271, the whole prefixCache at depth 11 and code 5506, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22019-201820", "node_context_12_22019_201820", "Original split at fuel 9 and node 201820",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 201720, 201783, 201810, 201819. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5506-203271", "node_context_11_5506_203271", "Original split at fuel 10 and node 203271",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 202677, 202800, 203107, 203270. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-22019-201820", "context_12_22019_201820", "Context at depth 12, code 22019, node 201820",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22019 and original node 201820, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_88076_201720, context_13_88077_201783, context_13_88078_201810, context_13_88079_201819.", DescribeRole.Theorem),
            Node("context-11-5506-203271", "context_11_5506_203271", "Context at depth 11, code 5506, node 203271",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5506 and original node 203271, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_22024_202677, context_12_22025_202800, context_12_22026_203107, context_12_22027_203270.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
