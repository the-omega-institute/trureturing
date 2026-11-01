using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0757Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0757.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0757",
        H("Original frontier context coverage 0757"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36340", "selected_cut_36340", "Selected cut at depth 12, code 288556, node 961982",
                "At remaining fuel 9 and original index 961982, selection on the full partial prefix of depth 12 and code 288556 returns the complete row with depth 12, base-four code 288556, original node 961982, kind 2, reserved field 0, 2937 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36387", "selected_cut_36387", "Selected cut at depth 12, code 288618, node 963745",
                "At remaining fuel 9 and original index 963745, selection on the full partial prefix of depth 12 and code 288618 returns the complete row with depth 12, base-four code 288618, original node 963745, kind 2, reserved field 0, 1949 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-72138-961929", "unmarked_context_11_72138_961929", "Unmarked parent at depth 11, code 72138",
                "The frontier Boolean is false at remaining fuel 10, original node 961929, the whole prefixCache at depth 11 and code 72138, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-72153-963681", "unmarked_context_11_72153_963681", "Unmarked parent at depth 11, code 72153",
                "The frontier Boolean is false at remaining fuel 10, original node 963681, the whole prefixCache at depth 11 and code 72153, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-72138-961929", "node_context_11_72138_961929", "Original split at fuel 10 and node 961929",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 961787, 961823, 961874, 961928. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-72153-963681", "node_context_11_72153_963681", "Original split at fuel 10 and node 963681",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 963634, 896706, 963654, 963680. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-72138-961929", "context_11_72138_961929", "Context at depth 11, code 72138, node 961929",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 72138 and original node 961929, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_288552_961787, context_12_288553_961823, context_12_288554_961874, context_12_288555_961928.", DescribeRole.Theorem),
            Node("context-12-288618-963745", "context_12_288618_963745", "Context at depth 12, code 288618, node 963745",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 288618 and original node 963745, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
