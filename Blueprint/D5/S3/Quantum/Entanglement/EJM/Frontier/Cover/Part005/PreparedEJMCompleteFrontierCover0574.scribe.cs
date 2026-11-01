using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0574Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0574.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0574",
        H("Original frontier context coverage 0574"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27556", "selected_cut_27556", "Selected cut at depth 12, code 91684, node 696507",
                "At remaining fuel 9 and original index 696507, selection on the full partial prefix of depth 12 and code 91684 returns the complete row with depth 12, base-four code 91684, original node 696507, kind 2, reserved field 0, 4017 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27602", "selected_cut_27602", "Selected cut at depth 13, code 366800, node 697353",
                "At remaining fuel 8 and original index 697353, selection on the full partial prefix of depth 13 and code 366800 returns the complete row with depth 13, base-four code 366800, original node 697353, kind 2, reserved field 0, 505 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-91683-696449", "unmarked_context_12_91683_696449", "Unmarked parent at depth 12, code 91683",
                "The frontier Boolean is false at remaining fuel 9, original node 696449, the whole prefixCache at depth 12 and code 91683, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22924-697346", "unmarked_context_11_22924_697346", "Unmarked parent at depth 11, code 22924",
                "The frontier Boolean is false at remaining fuel 10, original node 697346, the whole prefixCache at depth 11 and code 22924, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-91683-696449", "node_context_12_91683_696449", "Original split at fuel 9 and node 696449",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 696395, 696421, 696443, 696448. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22924-697346", "node_context_11_22924_697346", "Original split at fuel 10 and node 697346",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 697146, 697208, 697258, 697345. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-91683-696449", "context_12_91683_696449", "Context at depth 12, code 91683, node 696449",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 91683 and original node 696449, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_366732_696395, context_13_366733_696421, context_13_366734_696443, context_13_366735_696448.", DescribeRole.Theorem),
            Node("context-13-366800-697353", "context_13_366800_697353", "Context at depth 13, code 366800, node 697353",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 366800 and original node 697353, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
