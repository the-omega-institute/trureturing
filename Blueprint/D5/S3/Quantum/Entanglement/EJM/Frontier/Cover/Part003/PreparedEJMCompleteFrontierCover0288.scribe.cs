using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0288Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0288.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0288",
        H("Original frontier context coverage 0288"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13827", "selected_cut_13827", "Selected cut at depth 13, code 107700, node 361548",
                "At remaining fuel 8 and original index 361548, selection on the full partial prefix of depth 13 and code 107700 returns the complete row with depth 13, base-four code 107700, original node 361548, kind 2, reserved field 0, 645 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13874", "selected_cut_13874", "Selected cut at depth 13, code 107747, node 362301",
                "At remaining fuel 8 and original index 362301, selection on the full partial prefix of depth 13 and code 107747 returns the complete row with depth 13, base-four code 107747, original node 362301, kind 2, reserved field 0, 993 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26925-361592", "unmarked_context_12_26925_361592", "Unmarked parent at depth 12, code 26925",
                "The frontier Boolean is false at remaining fuel 9, original node 361592, the whole prefixCache at depth 12 and code 26925, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26936-362302", "unmarked_context_12_26936_362302", "Unmarked parent at depth 12, code 26936",
                "The frontier Boolean is false at remaining fuel 9, original node 362302, the whole prefixCache at depth 12 and code 26936, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26925-361592", "node_context_12_26925_361592", "Original split at fuel 9 and node 361592",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 361548, 361568, 361586, 361591. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26936-362302", "node_context_12_26936_362302", "Original split at fuel 9 and node 362302",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 362247, 362278, 362294, 362301. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-107700-361548", "context_13_107700_361548", "Context at depth 13, code 107700, node 361548",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 107700 and original node 361548, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-26936-362302", "context_12_26936_362302", "Context at depth 12, code 26936, node 362302",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26936 and original node 362302, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_107744_362247, context_13_107745_362278, context_13_107746_362294, context_13_107747_362301.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
