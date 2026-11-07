using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0319Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0319.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0319",
        H("Original frontier context coverage 0319"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15316", "selected_cut_15316", "Selected cut at depth 13, code 110800, node 393370",
                "At remaining fuel 8 and original index 393370, selection on the full partial prefix of depth 13 and code 110800 returns the complete row with depth 13, base-four code 110800, original node 393370, kind 2, reserved field 0, 437 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15361", "selected_cut_15361", "Selected cut at depth 12, code 27712, node 394179",
                "At remaining fuel 9 and original index 394179, selection on the full partial prefix of depth 12 and code 27712 returns the complete row with depth 12, base-four code 27712, original node 394179, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27699-393363", "unmarked_context_12_27699_393363", "Unmarked parent at depth 12, code 27699",
                "The frontier Boolean is false at remaining fuel 9, original node 393363, the whole prefixCache at depth 12 and code 27699, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-432-394178", "unmarked_context_9_432_394178", "Unmarked parent at depth 9, code 432",
                "The frontier Boolean is false at remaining fuel 12, original node 394178, the whole prefixCache at depth 9 and code 432, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27699-393363", "node_context_12_27699_393363", "Original split at fuel 9 and node 393363",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 393315, 393339, 393356, 393362. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-432-394178", "node_context_9_432_394178", "Original split at fuel 12 and node 394178",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 390869, 392058, 393179, 394177. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-27699-393363", "context_12_27699_393363", "Context at depth 12, code 27699, node 393363",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27699 and original node 393363, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_110796_393315, context_13_110797_393339, context_13_110798_393356, context_13_110799_393362.", DescribeRole.Theorem),
            Node("context-12-27712-394179", "context_12_27712_394179", "Context at depth 12, code 27712, node 394179",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27712 and original node 394179, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
