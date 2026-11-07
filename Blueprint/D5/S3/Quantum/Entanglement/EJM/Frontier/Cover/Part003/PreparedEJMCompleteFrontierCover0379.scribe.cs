using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0379Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0379.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0379",
        H("Original frontier context coverage 0379"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18196", "selected_cut_18196", "Selected cut at depth 13, code 284920, node 466196",
                "At remaining fuel 8 and original index 466196, selection on the full partial prefix of depth 13 and code 284920 returns the complete row with depth 13, base-four code 284920, original node 466196, kind 2, reserved field 0, 109 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18242", "selected_cut_18242", "Selected cut at depth 13, code 284987, node 467135",
                "At remaining fuel 8 and original index 467135, selection on the full partial prefix of depth 13 and code 284987 returns the complete row with depth 13, base-four code 284987, original node 467135, kind 2, reserved field 0, 885 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-71229-466193", "unmarked_context_12_71229_466193", "Unmarked parent at depth 12, code 71229",
                "The frontier Boolean is false at remaining fuel 9, original node 466193, the whole prefixCache at depth 12 and code 71229, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-71246-467136", "unmarked_context_12_71246_467136", "Unmarked parent at depth 12, code 71246",
                "The frontier Boolean is false at remaining fuel 9, original node 467136, the whole prefixCache at depth 12 and code 71246, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-71229-466193", "node_context_12_71229_466193", "Original split at fuel 9 and node 466193",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 466142, 466172, 466186, 466192. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-71246-467136", "node_context_12_71246_467136", "Original split at fuel 9 and node 467136",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 467106, 467127, 467135. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-71229-466193", "context_12_71229_466193", "Context at depth 12, code 71229, node 466193",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71229 and original node 466193, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_284916_466142, context_13_284917_466172, context_13_284918_466186, context_13_284919_466192.", DescribeRole.Theorem),
            Node("context-12-71246-467136", "context_12_71246_467136", "Context at depth 12, code 71246, node 467136",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71246 and original node 467136, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_284984_3444, context_13_284985_467106, context_13_284986_467127, context_13_284987_467135.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
